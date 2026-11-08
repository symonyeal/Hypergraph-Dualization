use std::fs;
use std::process::{Command, Stdio};

fn test_root() -> std::path::PathBuf {
    std::env::var_os("READONCE_TEST_ROOT").map(Into::into).unwrap_or_else(|| {
        std::env::current_exe().unwrap().parent().unwrap().to_path_buf()
    })
}

fn unique_dir(label: &str) -> std::path::PathBuf {
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let d = test_root().join(format!("readonce-dag-{label}-{}-{stamp}", std::process::id()));
    fs::create_dir(&d).unwrap();
    d
}

#[test]
fn overflow_fails_before_output() {
    let branches = (0..129)
        .map(|i| format!("(& {} {})", 2 * i, 2 * i + 1))
        .collect::<Vec<_>>();
    let input = format!("(| {})", branches.join(" "));
    let spill = unique_dir("overflow-spill");
    let out = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
        .args(["--classes", "--spill"])
        .arg(&spill)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    use std::io::Write;
    let mut child = out;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("dual term count exceeds u128"));
    assert_eq!(fs::read_dir(&spill).unwrap().count(), 0);
}

#[test]
fn spill_refuses_nonempty_directory_without_replacing_data() {
    let d = unique_dir("existing-spill");
    let keep = d.join("1.bin");
    fs::write(&keep, b"keep me").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
        .args(["--classes", "--spill"])
        .arg(&d)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    use std::io::Write;
    let mut child = output;
    child.stdin.take().unwrap().write_all(b"(& 0 1)").unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert_eq!(fs::read(&keep).unwrap(), b"keep me");
}

#[test]
fn representable_large_counts_do_not_overflow_split_test() {
    let pairs = (0..127)
        .map(|i| format!("(| {} {})", 2 * i, 2 * i + 1))
        .collect::<Vec<_>>();
    let input = format!("(& {} 254)", pairs.join(" "));
    let output = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
        .args(["--delta-only", "--leftmost"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    use std::io::Write;
    let mut child = output;
    child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let fields: Vec<u128> = String::from_utf8(output.stdout)
        .unwrap()
        .split_whitespace()
        .map(|field| field.parse().unwrap())
        .collect();
    assert_eq!(fields[1], (1u128 << 127) + 128);
    assert!(fields[2] > 1);

    // Its recursion tree exceeds u128 even though N fits.
    let mut child = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
        .arg("--leftmost")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
        .spawn().unwrap();
    child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("recursion tree count exceeds u128"));
}

#[test]
fn spill_and_memory_classes_match() {
    let input = "(& (| 0 1) (| 2 3))";
    let run = |spill: Option<&std::path::Path>| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_readonce_dag"));
        command.args(["--classes", "--leftmost"]);
        if let Some(d) = spill {
            command.arg("--spill").arg(d);
        }
        command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped());
        let mut child = command.spawn().unwrap();
        use std::io::Write;
        child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        output.stdout
    };
    let spill = unique_dir("valid-spill");
    assert_eq!(run(None), run(Some(&spill)));
}

#[test]
fn invalid_formulas_and_options_emit_no_result() {
    let cases: &[(&str, &[&str])] = &[
        ("(& 0 0)", &[]),
        ("(^ 0 1)", &[]),
        ("(& 0 1) (| 2 3)", &[]),
        ("(&)", &[]),
        ("(& 0", &[]),
        ("", &[]),
        ("512", &[]),
        ("xx0", &[]),
        ("(& 0 1)", &["--guardedd"]),
        ("(& 0 1)", &["--leftmost", "--guarded"]),
        ("(& 0 1)", &["--classes", "--iso"]),
        ("(& 0 1)", &["--spill"]),
        ("(& 0 1)", &["--spill", "--classes"]),
        ("(& 0 1)", &["--spill", "unused"]),
    ];
    for &(input, args) in cases {
        let mut child = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
            .args(args).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
            .spawn().unwrap();
        use std::io::Write;
        child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(!output.status.success(), "accepted {input:?} {args:?}");
        assert!(output.stdout.is_empty(), "published result for {input:?} {args:?}");
    }
}

#[test]
fn invalid_formula_does_not_start_spill_queue() {
    let spill = unique_dir("invalid-formula");
    let mut child = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
        .args(["--classes", "--spill"]).arg(&spill)
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
        .spawn().unwrap();
    use std::io::Write;
    child.stdin.take().unwrap().write_all(b"(& 0 0)").unwrap();
    let output = child.wait_with_output().unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert_eq!(fs::read_dir(&spill).unwrap().count(), 0);
}

#[test]
fn valid_sparse_and_prefixed_variables_agree() {
    let run = |input: &str| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_readonce_dag"))
            .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
            .spawn().unwrap();
        use std::io::Write;
        child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success());
        output.stdout
    };
    assert_eq!(run("(& 0 1)"), run("(& x0 x511)"));
}
