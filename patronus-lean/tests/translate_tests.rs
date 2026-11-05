use patronus::btor2;

#[test]
fn translate_swap() {
    let (ctx, sys) = btor2::parse_file("../inputs/unittest/aman_goel_4bit.btor").unwrap();
    let lean = patronus_lean::translate_to_str(&ctx, &sys);
    insta::assert_snapshot!(lean);
}
