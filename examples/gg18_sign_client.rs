#![allow(non_snake_case)]

use curv::{
    arithmetic::traits::*,
    cryptographic_primitives::{
        proofs::sigma_correct_homomorphic_elgamal_enc::HomoELGamalProof,
        proofs::sigma_dlog::DLogProof, secret_sharing::feldman_vss::VerifiableSS,
    },
    elliptic::curves::secp256_k1::{FE, GE},
    elliptic::curves::traits::ECScalar,
    BigInt,
};
use multi_party_ecdsa::protocols::multi_party_ecdsa::gg_2018::party_i::{
    Keys, LocalSignature, PartyPrivate, Phase5ADecom1, Phase5Com1, Phase5Com2, Phase5DDecom2,
    SharedKeys, SignBroadcastPhase1, SignDecommitPhase1, SignKeys,
};
use multi_party_ecdsa::utilities::mta::*;

use paillier::EncryptionKey;
use reqwest::Client;
use std::{env, fs, time};

mod common;
use common::{
    broadcast, check_sig, poll_for_broadcasts, poll_for_p2p, postb, sendp2p, Params, PartySignup,
};

#[allow(clippy::cognitive_complexity)]
fn main() {
    if env::args().nth(4).is_some() {
        panic!("too many arguments")
    }
    if env::args().nth(3).is_none() {
        panic!("too few arguments")
    }
    let message_str = env::args().nth(3).unwrap_or_else(|| "".to_string());
    let message = match hex::decode(message_str.clone()) {
        Ok(x) => x,
        Err(_e) => message_str.as_bytes().to_vec(),
    };
    let message = &message[..];
    let client = Client::new();
    // delay:
    let delay = time::Duration::from_millis(25);
    // read key file
    // 讀取完成 DKG 階段之後所存的資料，包含：
    // party_keys (ui , yi , dk , ek , index)、shared_keys (y , xi)、 party_id、 vss_scheme_vec (所有人的 vss commit，會有 n 組)、
    // paillier_key_vector (所有人的 paillier pub key，會有 n 組)、 y_sum (y)
    let data = fs::read_to_string(env::args().nth(2).unwrap())
        .expect("Unable to load keys, did you run keygen first? ");
    let (party_keys, shared_keys, party_id, vss_scheme_vec, paillier_key_vector, y_sum): (
        Keys,
        SharedKeys,
        u16,
        Vec<VerifiableSS<GE>>,
        Vec<EncryptionKey>,
        GE,
    ) = serde_json::from_str(&data).unwrap();

    //read parameters:
    // THRESHOLD = t，在[GG18] 的定義中，需要 t+1 人才能完成簽名
    let data = fs::read_to_string("params.json")
        .expect("Unable to read params, make sure config file is present in the same folder ");
    let params: Params = serde_json::from_str(&data).unwrap();
    let THRESHOLD = params.threshold.parse::<u16>().unwrap();

    //signup:
    let (party_num_int, uuid) = match signup(&client).unwrap() {
        PartySignup { number, uuid } => (number, uuid),
    };
    println!("number: {:?}, uuid: {:?}", party_num_int, uuid);

    // Round 0
    // round 0: collect signers IDs
    // 要確認參與簽名的節點有哪些，這會影響 λi 的計算
    assert!(broadcast(
        &client,
        party_num_int,
        "round0",
        serde_json::to_string(&party_id).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round0_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round0",
        uuid.clone(),
    );

    let mut j = 0;
    let mut signers_vec: Vec<usize> = Vec::new();
    for i in 1..=THRESHOLD + 1 {
        if i == party_num_int {
            signers_vec.push((party_id - 1) as usize);
        } else {
            let signer_j: u16 = serde_json::from_str(&round0_ans_vec[j]).unwrap();
            signers_vec.push((signer_j - 1) as usize);
            j += 1;
        }
    }
   
    // private 裡面有 Pi 自己的 ui , xi , dk
    let private = PartyPrivate::set_private(party_keys.clone(), shared_keys);
   
    // sign_keys 有 wi (xi*λi), Wi (wi*G) , ki , γi , γi*G
    let sign_keys = SignKeys::create(
        &private,
        &vss_scheme_vec[signers_vec[(party_num_int - 1) as usize]],
        signers_vec[(party_num_int - 1) as usize],
        &signers_vec,
    );

    // 利用 vee_scheme 計算出”每個節點“的 xi_com (也就是 xi*G)
    let xi_com_vec = Keys::get_commitments_to_xi(&vss_scheme_vec);
    //////////////////////////////////////////////////////////////////////////////
    
    // Round 1
    // com：對 γi*G 的 hash commitment
    // decom：γi*G , blind factor
    let (com, decommit) = sign_keys.phase1_broadcast();
    // m_a_k：在兩個 MtA 階段中， Pi 都會先扮演 alice 角色，傳送 Enc_eki(ki) (也就是用 Pi 自己的
    // Paillier 公鑰對 ki 加密) 給其他節點。以 P1 為例，他傳給 P2 , ... , Pt 的 m_a_k 都一樣，所
    // 以在 round 1 是採用 broadcast
    let (m_a_k, _) = MessageA::a(&sign_keys.k_i, &party_keys.ek, &[]);
    assert!(broadcast(
        &client,
        party_num_int,
        "round1",
        serde_json::to_string(&(com.clone(), m_a_k.clone())).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round1_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round1",
        uuid.clone(),
    );

    // bc1_vec 裡面放 com
    // m_a_vec 裡面放 round 1 收到的所有 m_a_k (共 t 個)
    let mut j = 0;
    let mut bc1_vec: Vec<SignBroadcastPhase1> = Vec::new();
    let mut m_a_vec: Vec<MessageA> = Vec::new();

    for i in 1..THRESHOLD + 2 {
        if i == party_num_int {
            bc1_vec.push(com.clone());
        //   m_a_vec.push(m_a_k.clone());
        } else {
            //     if signers_vec.contains(&(i as usize)) {
            let (bc1_j, m_a_party_j): (SignBroadcastPhase1, MessageA) =
                serde_json::from_str(&round1_ans_vec[j]).unwrap();
            bc1_vec.push(bc1_j);
            m_a_vec.push(m_a_party_j);

            j += 1;
            //       }
        }
    }
    assert_eq!(signers_vec.len(), bc1_vec.len());

    //////////////////////////////////////////////////////////////////////////////
    // 先執行 kj*γi 的 MtA，接著執行 kj*wi 的 MtAwc (在 [GG19] 中，這兩個都是 MtAwc)
    // 在這邊 Pi 要扮演 MtA 裡 bob 的角色，使用 Pj 的 Paillier 公鑰，將 round 1 從其他節點 
    // 收到的 t 個 m_a_k，利用 Paillier 同態運算，計算 Enc_ekj(kj*γi+β‘)，最後再令 β = -β'
    // m_b 包含對 b 以及 β' 的 dlog_proof (可參考 multi-party-ecdsa/src/utilities/mta/mod.rs line 41)
    let mut m_b_gamma_send_vec: Vec<MessageB> = Vec::new();
    let mut beta_vec: Vec<FE> = Vec::new();
    let mut m_b_w_send_vec: Vec<MessageB> = Vec::new();
    let mut ni_vec: Vec<FE> = Vec::new();
    let mut j = 0;
    for i in 1..THRESHOLD + 2 {
        if i != party_num_int {
            let (m_b_gamma, beta_gamma, _, _) = MessageB::b(
                &sign_keys.gamma_i,
                &paillier_key_vector[signers_vec[(i - 1) as usize]],
                m_a_vec[j].clone(),
                &[],
            )
            .unwrap();
    // 在這邊 Pi 要扮演 MtA 裡 bob 的角色，使用 Pj 的 Paillier 公鑰，將 round 1 從其他節點 
    // 收到的 t 個 m_a_k，利用 Paillier 同態運算，計算 Enc_ekj(kj*wi+ν‘)，最後再令 ν = -ν'
            let (m_b_w, beta_wi, _, _) = MessageB::b(
                &sign_keys.w_i,
                &paillier_key_vector[signers_vec[(i - 1) as usize]],
                m_a_vec[j].clone(),
                &[],
            )
            .unwrap();
            m_b_gamma_send_vec.push(m_b_gamma);
            m_b_w_send_vec.push(m_b_w);
            beta_vec.push(beta_gamma);
            ni_vec.push(beta_wi);
            j += 1;
        }
    }
   
   // Round 2
   // 因為對應不同 Pj，Pi 計算出的 m_b_xxx_send 各不相同，所以在 round 2 會採用 p2p 傳送
    let mut j = 0;
    for i in 1..THRESHOLD + 2 {
        if i != party_num_int {
            assert!(sendp2p(
                &client,
                party_num_int,
                i,
                "round2",
                serde_json::to_string(&(m_b_gamma_send_vec[j].clone(), m_b_w_send_vec[j].clone()))
                    .unwrap(),
                uuid.clone()
            )
            .is_ok());
            j += 1;
        }
    }

    let round2_ans_vec = poll_for_p2p(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round2",
        uuid.clone(),
    );

    // m_b_xxx_rec_vec 裡面放的是 Pi 身為 alice 角色，從其他 t 個節點那邊收到
    // 的 m_b，這些 m_b 是用 Pi 的 Paillier 公鑰加密。不要跟 m_b_gamma_send 搞混
    let mut m_b_gamma_rec_vec: Vec<MessageB> = Vec::new();
    let mut m_b_w_rec_vec: Vec<MessageB> = Vec::new();

    for i in 0..THRESHOLD {
        //  if signers_vec.contains(&(i as usize)) {
        let (m_b_gamma_i, m_b_w_i): (MessageB, MessageB) =
            serde_json::from_str(&round2_ans_vec[i as usize]).unwrap();
        m_b_gamma_rec_vec.push(m_b_gamma_i);
        m_b_w_rec_vec.push(m_b_w_i);
        //     }
    }

    let mut alpha_vec: Vec<FE> = Vec::new();
    let mut miu_vec: Vec<FE> = Vec::new();

    let mut j = 0;
    for i in 1..THRESHOLD + 2 {
        if i != party_num_int {
            let m_b = m_b_gamma_rec_vec[j].clone();

    // 在 verify_proofs_get_alpha 中，會做兩件事：
    // 1.利用 Pi 自己的 Paillier 私鑰對 m_b_j 解密，得到 α_ij，計算 α_ij*G
    // 2.前面有提過，m_b 包含 b 和 β' 的 dlog_proof，而 dlog_proof 中又會包含 
    //   b 和 β'分別乘上 G 的值 (b_pk , β'_pk)，Pi 計算 b_pk*ki + β'_pk
    // 最後比較前面兩步驟得到的值，若相同，則 Pi 相信他收到的 α_ij_xxx 是正確的
            let alpha_ij_gamma = m_b
                .verify_proofs_get_alpha(&party_keys.dk, &sign_keys.k_i)
                .expect("wrong dlog or m_b");
            let m_b = m_b_w_rec_vec[j].clone();
            let alpha_ij_wi = m_b
                .verify_proofs_get_alpha(&party_keys.dk, &sign_keys.k_i)
                .expect("wrong dlog or m_b");
            alpha_vec.push(alpha_ij_gamma.0);
            miu_vec.push(alpha_ij_wi.0);
            
            // update_commitments_to_xi：把 xi*G 乘上 λi
            let g_w_i = Keys::update_commitments_to_xi(
                &xi_com_vec[signers_vec[(i - 1) as usize]],
                &vss_scheme_vec[signers_vec[(i - 1) as usize]],
                signers_vec[(i - 1) as usize],
                &signers_vec,
            );
            assert_eq!(m_b.b_proof.pk, g_w_i);
            j += 1;
        }
    }
    //////////////////////////////////////////////////////////////////////////////
    // delta_i = ( ki * γi ) + αij + βji 
    // sigma = ( ki * wi ) + µij + νji
    // note：這裡的 sigma 應該就是 sigma_i
    let delta_i = sign_keys.phase2_delta_i(&alpha_vec, &beta_vec);
    let sigma = sign_keys.phase2_sigma_i(&miu_vec, &ni_vec);

    // Round 3 廣播 delta_i 
    assert!(broadcast(
        &client,
        party_num_int,
        "round3",
        serde_json::to_string(&delta_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round3_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round3",
        uuid.clone(),
    );
    let mut delta_vec: Vec<FE> = Vec::new();
    format_vec_from_reads(
        &round3_ans_vec,
        party_num_int as usize,
        delta_i,
        &mut delta_vec,
    );
    
    // delta_inv = (∑δi )^-1 = (kγ)^-1
    let delta_inv = SignKeys::phase3_reconstruct_delta(&delta_vec);

    //////////////////////////////////////////////////////////////////////////////
    // Round 4 廣播 decommit (在 round 1 生成)
    // decommit to gamma_i (應該是對 γi*G 的 decommit 吧 ？)
    assert!(broadcast(
        &client,
        party_num_int,
        "round4",
        serde_json::to_string(&decommit).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round4_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round4",
        uuid.clone(),
    );

    let mut decommit_vec: Vec<SignDecommitPhase1> = Vec::new();
    format_vec_from_reads(
        &round4_ans_vec,
        party_num_int as usize,
        decommit,
        &mut decommit_vec,
    );
    // 將 Pi 自己的 decommit 設為 decomm_i，並從 decommit_vec 中移除
    let decomm_i = decommit_vec.remove((party_num_int - 1) as usize);
    // 將 Pi 自己的 com (對 γi*G 的 commitment，在 round 1 生成) 從 bec_vec 中移除
    bc1_vec.remove((party_num_int - 1) as usize);
    let b_proof_vec = (0..m_b_gamma_rec_vec.len())
        .map(|i| &m_b_gamma_rec_vec[i].b_proof)
        .collect::<Vec<&DLogProof<GE>>>();
    
    // 先驗證 b_proof 裡的 pk 和 decommit_vec[i] 的 g_gamma_i 是否相等，再接著驗證 hash commitment
    // 驗證通過之後，計算 R = ( ∑Γi )*δ^-1。要注意的是，這邊的 g_gamma_i 不包含 Pi 自己的，因為
    // decommit_vec 已經將其移除掉了
    let R = SignKeys::phase4(&delta_inv, &b_proof_vec, decommit_vec, &bc1_vec)
        .expect("bad gamma_i decommit");

    // 所以 R 要再加上 Pi 自己的 g_gamma_i * delta_inv
    // adding local g_gamma_i
    let R = R + decomm_i.g_gamma_i * delta_inv;

    // we assume the message is already hashed (by the signer).
    let message_bn = BigInt::from_bytes(message);
    
    // 包含 l_i , rho_i , r (R 的 x 座標) , s_i (m*k_i + r*sigma_i;) , m , y
    let local_sig =
        LocalSignature::phase5_local_sig(&sign_keys.k_i, &message_bn, &R, &sigma, &y_sum);

    // phase5_com, phase_5a_decom：
    // 計算 A_i = rho_i*G , B_i = G * l_i_rho_i = l_i*A_i , V_i = s_i*R + l_i*G
    // 令 input_hash = hash(A_i , B_i , V_i)，再對 input_hash 做 hash commitment
    // helgamal_proof：
    // 對 A_i , R , G , V_i , B_i 做 homoElgamal proof， witness = (r,x) = (l_i,x_i)
    // 目標要證明 V_i = x*R+r*G , B_i = r*A_i。細節可參考：curv/src/cryptographic_primitives/proofs/sigma_correct_homomorphic_elgamal_enc.rs
    // dlog_proof_rho：
    // 對 rho_i 做 dlog_proof
    let (phase5_com, phase_5a_decom, helgamal_proof, dlog_proof_rho) =
        local_sig.phase5a_broadcast_5b_zkproof();

    // Round 5 廣播 phase5_com (對 A_i , B_i , V_i 的 commitment)
    // phase (5A)  broadcast commit
    assert!(broadcast(
        &client,
        party_num_int,
        "round5",
        serde_json::to_string(&phase5_com).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round5_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round5",
        uuid.clone(),
    );

    let mut commit5a_vec: Vec<Phase5Com1> = Vec::new();
    format_vec_from_reads(
        &round5_ans_vec,
        party_num_int as usize,
        phase5_com,
        &mut commit5a_vec,
    );

    // Round 6 廣播 phase_5a_decom (A_i , B_i , V_i 加上 blind_factor) 
    // 以及 helgamal_proof 和 dlog_proof_rho
    //phase (5B)  broadcast decommit and (5B) ZK proof
    assert!(broadcast(
        &client,
        party_num_int,
        "round6",
        serde_json::to_string(&(
            phase_5a_decom.clone(),
            helgamal_proof.clone(),
            dlog_proof_rho.clone()
        ))
        .unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round6_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round6",
        uuid.clone(),
    );

    // 把這三樣東西串在一起
    let mut decommit5a_and_elgamal_and_dlog_vec: Vec<(
        Phase5ADecom1,
        HomoELGamalProof<GE>,
        DLogProof<GE>,
    )> = Vec::new();
    format_vec_from_reads(
        &round6_ans_vec,
        party_num_int as usize,
        (
            phase_5a_decom.clone(),
            helgamal_proof.clone(),
            dlog_proof_rho.clone(),
        ),
        &mut decommit5a_and_elgamal_and_dlog_vec,
    );
    let decommit5a_and_elgamal_and_dlog_vec_includes_i =
        decommit5a_and_elgamal_and_dlog_vec.clone();
    
    // 將 Pi 自己的東西移除
    decommit5a_and_elgamal_and_dlog_vec.remove((party_num_int - 1) as usize);
    commit5a_vec.remove((party_num_int - 1) as usize);
    let phase_5a_decomm_vec = (0..THRESHOLD)
        .map(|i| decommit5a_and_elgamal_and_dlog_vec[i as usize].0.clone())
        .collect::<Vec<Phase5ADecom1>>();
    let phase_5a_elgamal_vec = (0..THRESHOLD)
        .map(|i| decommit5a_and_elgamal_and_dlog_vec[i as usize].1.clone())
        .collect::<Vec<HomoELGamalProof<GE>>>();
    let phase_5a_dlog_vec = (0..THRESHOLD)
        .map(|i| decommit5a_and_elgamal_and_dlog_vec[i as usize].2.clone())
        .collect::<Vec<DLogProof<GE>>>();
    
    // phase5c 在 multi-party-ecdsa/src/protocols/multi_party_ecdsa/gg_2018/party_i.rs line 555
    // 先驗證 hash commitment 以及其餘 zk proof
    // 計算 v = -mG-rY+sum (vi)，其中 sum (vi) 有包含 Pi 的值，因為 fold 的 base point 是 v_i (來自 phase_5a_decom.V_i)
    // 計算 a = ∑A_i，這邊就不包含 Pi 的值
    // 計算 u_i = v*rho_i , t_i = a*l_i
    // phase5_com2：對 u_i , t_i 做 hash commitment
    // phase_5d_decom2：u_i , t_i , blind factor
    let (phase5_com2, phase_5d_decom2) = local_sig
        .phase5c(
            // 前四樣裡頭都沒有 Pi 的東西
            &phase_5a_decomm_vec,
            &commit5a_vec,
            &phase_5a_elgamal_vec,
            &phase_5a_dlog_vec,
            // phase_5a_decom 來自 round 4 line 375，Pi 的資料並沒有被移除
            // 可以注意到，這裡是 _deco'm'，line 464 有被移除的是 _deco'mm'
            &phase_5a_decom.V_i,
            &R,
        )
        .expect("error phase5");

    //////////////////////////////////////////////////////////////////////////////
    // Round 7 廣播 phase5_com2 (對 u_i , t_i 做 hash commitment)
    assert!(broadcast(
        &client,
        party_num_int,
        "round7",
        serde_json::to_string(&phase5_com2).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round7_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round7",
        uuid.clone(),
    );

    let mut commit5c_vec: Vec<Phase5Com2> = Vec::new();
    format_vec_from_reads(
        &round7_ans_vec,
        party_num_int as usize,
        phase5_com2,
        &mut commit5c_vec,
    );

    // Round 8 廣播 phase_5d_decom2 (u_i , t_i 和 blind factor) , 
    //phase (5B)  broadcast decommit and (5B) ZK proof
    assert!(broadcast(
        &client,
        party_num_int,
        "round8",
        serde_json::to_string(&phase_5d_decom2).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round8_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round8",
        uuid.clone(),
    );

    let mut decommit5d_vec: Vec<Phase5DDecom2> = Vec::new();
    format_vec_from_reads(
        &round8_ans_vec,
        party_num_int as usize,
        phase_5d_decom2.clone(),
        &mut decommit5d_vec,
    );

    // 這邊是有包含 Pi 的資料的，在 line 446 有先另外找地方放
    let phase_5a_decomm_vec_includes_i = (0..=THRESHOLD)
        .map(|i| {
            decommit5a_and_elgamal_and_dlog_vec_includes_i[i as usize]
                .0
                .clone()
        })
        .collect::<Vec<Phase5ADecom1>>();
    
    // 先驗證 commit5c_vec (也就是 phase5_com2，對 u_i , t_i 做 hash commitment)
    // 驗證 G + ∑t_i + ∑b_i - ∑u_i 會不會等於 G
    // 這邊其實跟 protocol 是一樣的，只是因為有沒有包含 Pi 資料的關係，才會看起來有點複雜
    let s_i = local_sig
        .phase5d(
            &decommit5d_vec,
            &commit5c_vec,
            &phase_5a_decomm_vec_includes_i,
        )
        .expect("bad com 5d");

    //////////////////////////////////////////////////////////////////////////////
    // Round 9 廣播 s_i
    assert!(broadcast(
        &client,
        party_num_int,
        "round9",
        serde_json::to_string(&s_i).unwrap(),
        uuid.clone()
    )
    .is_ok());
    let round9_ans_vec = poll_for_broadcasts(
        &client,
        party_num_int,
        THRESHOLD + 1,
        delay,
        "round9",
        uuid.clone(),
    );

    let mut s_i_vec: Vec<FE> = Vec::new();
    format_vec_from_reads(&round9_ans_vec, party_num_int as usize, s_i, &mut s_i_vec);

    s_i_vec.remove((party_num_int - 1) as usize);
    // 在生成簽名的階段，會檢查 recovery id，以及 s 是否小於 n/2
    let sig = local_sig
        .output_signature(&s_i_vec)
        .expect("verification failed");
    println!("party {:?} Output Signature: \n", party_num_int);
    println!("R: {:?}", sig.r.get_element());
    println!("s: {:?} \n", sig.s.get_element());
    println!("recid: {:?} \n", sig.recid.clone());

    let sign_json = serde_json::to_string(&(
        "r",
        (BigInt::from_bytes(&(sig.r.get_element())[..])).to_str_radix(16),
        "s",
        (BigInt::from_bytes(&(sig.s.get_element())[..])).to_str_radix(16),
    ))
    .unwrap();

    // check sig against secp256k1
    check_sig(&sig.r, &sig.s, &message_bn, &y_sum);

    fs::write("signature".to_string(), sign_json).expect("Unable to save !");
}

fn format_vec_from_reads<'a, T: serde::Deserialize<'a> + Clone>(
    ans_vec: &'a [String],
    party_num: usize,
    value_i: T,
    new_vec: &'a mut Vec<T>,
) {
    let mut j = 0;
    for i in 1..ans_vec.len() + 2 {
        if i == party_num {
            new_vec.push(value_i.clone());
        } else {
            let value_j: T = serde_json::from_str(&ans_vec[j]).unwrap();
            new_vec.push(value_j);
            j += 1;
        }
    }
}

pub fn signup(client: &Client) -> Result<PartySignup, ()> {
    let key = "signup-sign".to_string();

    let res_body = postb(&client, "signupsign", key).unwrap();
    serde_json::from_str(&res_body).unwrap()
}
