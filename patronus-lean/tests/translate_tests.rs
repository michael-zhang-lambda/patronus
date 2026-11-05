use patronus::btor2;

#[test]
fn translate_aman_goel_4bit() {
    let (ctx, sys) = btor2::parse_file("../inputs/unittest/aman_goel_4bit.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_aman_goel_16bit() {
    let (ctx, sys) = btor2::parse_file("../inputs/unittest/aman_goel_16bit.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_swap() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Swap.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_delay() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Delay.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_overflow() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Overflow.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}
