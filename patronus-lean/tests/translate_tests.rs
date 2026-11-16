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

#[test]
fn translate_accumulate() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Accumulate.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_memory() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Memory.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_memory_init() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/MemoryInit.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_memory_pair() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/MemoryPair.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_memory_unsafe() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/MemoryUnsafe.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_array_equal() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/ArrayEqual.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_arith() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Arith.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_bitwise() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Bitwise.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_compare() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Compare.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_shift() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Shift.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_extend() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Extend.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_divide() {
    let (ctx, sys) = btor2::parse_file("../inputs/verilog_tests/Divide.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

/// `implies` and `smod` are never emitted by yosys, so they are tested with inline BTOR.
#[test]
fn translate_implies_smod() {
    let src = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 a
4 input 1 b
5 state 1 m
6 smod 1 3 4
7 next 1 5 6
8 eq 2 3 4
9 ugte 2 3 4
10 implies 2 8 9
11 not 2 10
12 bad 11
";
    let mut ctx = patronus::expr::Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("ImpliesSmod")).unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}

/// yosys never emits whole-array `eq`, so array equality is tested with inline BTOR:
/// two zero-initialized memories receive identical writes; bad if they differ.
#[test]
fn translate_array_equal_inline() {
    let src = "\
1 sort bitvec 2
2 sort bitvec 4
3 sort array 1 2
4 sort bitvec 1
5 input 1 a
6 input 2 d
7 const 2 0000
8 state 3 m1
9 state 3 m2
10 init 3 8 7
11 init 3 9 7
12 write 3 8 5 6
13 write 3 9 5 6
14 next 3 8 12
15 next 3 9 13
16 eq 4 8 9
17 not 4 16
18 bad 17
";
    let mut ctx = patronus::expr::Context::default();
    let sys = btor2::parse_str(&mut ctx, src, Some("ArrayEqualInline")).unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}
