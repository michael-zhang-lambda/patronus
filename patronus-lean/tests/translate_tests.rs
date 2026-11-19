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

/// Inline BTOR with two constraints: one over an input only, one mixing state and input.
const CONSTRAINT_SRC: &str = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 a
4 state 1 x
5 const 1 0000
6 init 1 4 5
7 add 1 4 3
8 next 1 4 7
9 const 1 0011
10 ult 2 3 9
11 constraint 10
12 ulte 2 4 7
13 constraint 12
14 const 1 1111
15 eq 2 4 14
16 bad 15
";

/// Inline BTOR with states that have an `init` but no `next` (one named, one unnamed).
/// The BTOR2 parser only demotes states with neither `init` nor `next` to inputs, so these
/// reach the translator as states: they keep their `init` and get a `$next` input that
/// supplies their value in the following cycle.
const NO_NEXT_SRC: &str = "\
1 sort bitvec 4
2 sort bitvec 1
3 input 1 a
4 state 1 x
5 state 1 free
6 state 2
7 add 1 4 3
8 next 1 4 7
9 add 1 4 5
10 ugt 2 9 4
11 and 2 10 6
12 bad 11
13 const 1 0101
14 init 1 5 13
15 const 2 1
16 init 2 6 15
";

#[test]
fn translate_constraint() {
    let mut ctx = patronus::expr::Context::default();
    let sys = btor2::parse_str(&mut ctx, CONSTRAINT_SRC, Some("Constraint")).unwrap();
    assert_eq!(sys.constraints.len(), 2);
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    // constraint body references `s` and `i`, so the lambda must bind them
    assert!(lean.contains("constraint := fun (s : State) (i : Input) => ("));
    assert!(lean.contains("i.«a»") && lean.contains("s.«x»"));
    insta::assert_snapshot!(lean);
}

#[test]
fn translate_no_constraint_is_true() {
    let mut ctx = patronus::expr::Context::default();
    let sys = btor2::parse_str(&mut ctx, NO_NEXT_SRC, Some("NoNext")).unwrap();
    assert!(sys.constraints.is_empty());
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    assert!(lean.contains("constraint := fun (s : State) (i : Input) => (\n    true\n  ),"));
}

#[test]
fn signal_names_no_next_states_get_next_inputs() {
    let mut ctx = patronus::expr::Context::default();
    let sys = btor2::parse_str(&mut ctx, NO_NEXT_SRC, Some("NoNext")).unwrap();
    let (states, inputs) = patronus_lean::signal_names(&ctx, &sys);

    // next-less states remain states, in declaration order
    let state_names: Vec<_> = states.iter().map(|(_, n)| n.as_str()).collect();
    assert_eq!(state_names, ["x", "free", "_state_0"]);

    // regular inputs first, then one `$next` input per next-less state in declaration order
    let input_names: Vec<_> = inputs.iter().map(|(_, n)| n.as_str()).collect();
    assert_eq!(input_names, ["a", "free$next", "_state_0$next"]);

    // each `$next` input is keyed by the symbol of the state it feeds
    assert_eq!(inputs[1].0, states[1].0.symbol);
    assert_eq!(inputs[2].0, states[2].0.symbol);
}

#[test]
fn translate_no_next_state() {
    let mut ctx = patronus::expr::Context::default();
    let sys = btor2::parse_str(&mut ctx, NO_NEXT_SRC, Some("NoNext")).unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    let (state_struct, rest) = lean.split_once("structure Input where").unwrap();
    let (input_struct, _) = rest.split_once("def NoNext_sys").unwrap();
    assert!(state_struct.contains("«free» : BitVec 4"));
    assert!(state_struct.contains("«_state_0» : BitVec 1"));
    assert!(input_struct.contains("«free$next» : BitVec 4"));
    assert!(input_struct.contains("«_state_0$next» : BitVec 1"));
    assert!(!input_struct.contains("«free» :"));
    // init is honored, next value comes from the `$next` input
    assert!(lean.contains("«free» := 5#4"));
    assert!(lean.contains("«_state_0» := 1#1"));
    assert!(lean.contains("«free» := i.«free$next»"));
    assert!(lean.contains("«_state_0» := i.«_state_0$next»"));
    // everything else reads the state, never the input directly
    assert!(lean.contains("s.«free»") && !lean.contains("i.«free»"));
    insta::assert_snapshot!(lean);
}
