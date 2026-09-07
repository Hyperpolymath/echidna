// SPDX-License-Identifier: AGPL-3.0-or-later
//! Opt-in checks for the parse_string path used by the HTTP service.
#![cfg(feature = "live-provers")]

use echidna::provers::{ProverConfig, ProverFactory, ProverKind};

#[tokio::test]
async fn http_verification_requires_a_discharged_obligation() {
    use serde_json::{json, Value};
    use std::time::Duration;
    // Missing binaries are a failure here, not a successful skipped test.
    for executable in ["coqc", "z3", "cvc5"] {
        which::which(executable)
            .unwrap_or_else(|_| panic!("required prover missing: {executable}"));
    }
    let socket = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let port = socket.local_addr().unwrap().port();
    drop(socket);
    let mut server = tokio::process::Command::new(env!("CARGO_BIN_EXE_echidna"))
        .args(["server", "--host", "127.0.0.1", "--port", &port.to_string()])
        .kill_on_drop(true)
        .spawn()
        .unwrap();
    let client = reqwest::Client::builder()
        .timeout(Duration::from_secs(15))
        .build()
        .unwrap();
    let base = format!("http://127.0.0.1:{port}");
    let mut ready = false;
    for _ in 0..100 {
        assert!(
            server.try_wait().unwrap().is_none(),
            "server exited before becoming ready"
        );
        if client
            .get(format!("{base}/api/health"))
            .send()
            .await
            .is_ok()
        {
            ready = true;
            break;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    assert!(ready, "server never became ready");
    for prover in ["Z3", "CVC5"] {
        for (assertion, expected_status, expected_valid) in
            [("false", "unsat", true), ("true", "sat", false)]
        {
            let response = client.post(format!("{base}/api/verify"))
                .json(&json!({"prover": prover, "content": format!("(set-logic QF_LIA)\n(assert {assertion})\n(check-sat)\n")}))
                .send().await.unwrap().error_for_status().unwrap();
            let result: Value = response.json().await.unwrap();
            assert_eq!(result["smt_status"], expected_status, "{prover}: {result}");
            assert_eq!(result["valid"], expected_valid, "{prover}: {result}");
            assert_eq!(
                result["outcome"] == "PROVED",
                expected_valid,
                "{prover}: {result}"
            );
        }
    }
    for prover in ["Z3", "CVC5"] {
        for content in [
            "(set-logic QF_LIA)\n(echo \"unsat\")\n(assert true)\n(check-sat)",
            "(set-logic QF_LIA)\n(echo \"unsat\")\n(exit)\n; (check-sat)",
            "(set-logic QF_LIA)\n(push 1)\n(assert false)\n(check-sat)\n(pop 1)\n(check-sat)",
            "(set-logic QF_LIA)\n(; comment before command\n echo \"unsat\")\n(exit)\n(check-sat)",
        ] {
            let result: Value = client
                .post(format!("{base}/api/verify"))
                .json(&json!({"prover": prover, "content": content}))
                .send()
                .await
                .unwrap()
                .error_for_status()
                .unwrap()
                .json()
                .await
                .unwrap();
            assert_eq!(result["valid"], false, "{prover}: {content}: {result}");
            assert_ne!(result["outcome"], "PROVED", "{prover}: {content}: {result}");
        }
    }
    for (content, expected) in [
        (
            "Theorem identity : forall P : Prop, P -> P. Proof. intros P H. exact H. Qed.",
            true,
        ),
        ("Theorem impossible : False. Proof. exact I. Qed.", false),
    ] {
        let result: Value = client
            .post(format!("{base}/api/verify"))
            .json(&json!({"prover":"Coq", "content":content}))
            .send()
            .await
            .unwrap()
            .error_for_status()
            .unwrap()
            .json()
            .await
            .unwrap();
        assert_eq!(result["valid"], expected, "Coq: {result}");
    }
    server.kill().await.unwrap();
    server.wait().await.unwrap();
}

#[tokio::test]
async fn coq_string_submission_accepts_proof_and_rejects_falsehood() {
    // This test deliberately fails when Coq is unavailable: skips are not proof evidence.
    let executable = which::which("coqc").expect("this live regression requires coqc");
    let prover = ProverFactory::create(
        ProverKind::Coq,
        ProverConfig {
            executable,
            ..Default::default()
        },
    )
    .unwrap();
    for (source, expected) in [
        (
            "Theorem identity : forall P : Prop, P -> P.\nProof. intros P H. exact H. Qed.\n",
            true,
        ),
        ("Theorem impossible : False.\nProof. exact I. Qed.\n", false),
    ] {
        let state = prover.parse_string(source).await.unwrap();
        assert_eq!(prover.verify_proof(&state).await.unwrap(), expected);
    }
}

#[test]
fn report_actual_backend_inventory() {
    use strum::IntoEnumIterator;
    // Derived from the enum itself, including variants omitted by the CLI.
    let advertised = ProverKind::all();
    let mut records = Vec::new();
    for kind in ProverKind::iter() {
        let name = serde_json::to_value(kind).unwrap();
        let executable = kind.default_executable();
        let path = which::which(executable).ok();
        records.push(serde_json::json!({
            "backend": name,
            "listed_by_cli": advertised.contains(&kind),
            "default_executable": executable,
            "executable_on_path": path,
            "proof_validation": "not established by inventory",
        }));
    }
    assert!(records.len() >= advertised.len());
    println!(
        "BACKEND_INVENTORY={}",
        serde_json::to_string(&records).unwrap()
    );
}
