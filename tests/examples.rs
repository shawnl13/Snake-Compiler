#![allow(warnings)]
use snake::runner;

macro_rules! mk_test {
    ($test_name:ident, $file_name:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_file($file_name, $expected_output)
        }
    };
}

macro_rules! mk_fail_test {
    ($test_name:ident, $file_name:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_fail($file_name, $expected_output)
        }
    };
}

/*
 * YOUR TESTS GO HERE
 */

// egg eater tests
//mk_test!(egg_interesting, "interesting,egg", 42);
//mk_test!(egg_other, "egg/other.egg", 2);
//mk_test!(egg_apply_to_five, "egg/applyToFive.egg", "6");
mk_test!(egg_array_simple, "egg/array_simple.egg", "5");
mk_test!(egg_chain_array_set, "egg/chain_array_set.egg", "5");
mk_test!(egg_chain_array_set_complicated, "egg/chain_array_set copy.egg", "0");
//
//mk_fail_test!(egg_call_non_fun_err, "egg/call_bool_err.egg", "called a non-function");
//mk_fail_test!(egg_arity_err, "egg/arity_err.egg", "wrong number of arguments");
mk_test!(egg_create_array, "egg/create_array.egg", "1");

mk_fail_test!(egg_index_non_array_err, "egg/index_non_array_err.egg", "indexed into non-array");
mk_fail_test!(egg_index_not_number_err, "egg/index_not_number_err.egg", "index not a number");
mk_fail_test!(egg_index_bounds_err, "egg/index_bounds_err.egg", "index out of bounds");

//mk_fail_test!(egg_len_not_array_err, "egg/len_err.egg", "length called with non-array");



// diamondback tests
mk_test!(diamondback_non_tail_fun, "dia/non_tail_fun.dia", "6");
mk_test!(diamondback_even_odd_240, "dia/even_odd.dia", "true");
mk_test!(diamondback_even_odd_240000, "dia/even_odd_big.dia", "true");
mk_test!(diamondback_non_max_fun, "dia/test_max.dia", "80");
mk_fail_test!(diamondback_err_dup_fun_name, "dia/dup_fun.dia", ""); 
mk_fail_test!(diamondback_err_dup_parameter, "dia/dup_para.dia", "");
mk_fail_test!(diamondback_err_arity, "dia/err_arity.dia", "");
mk_test!(diamondback_test_tail_lecture, "dia/test_tail_lecture.dia", "35");
mk_test!(diamondback_shadow_regression, "dia/many_bindings.boa", "20");
mk_test!(diamondback_shadow_regression2, "dia/let_regression.boa", "2");




// cobra tests:
mk_test!(cobra_test_if_simple, "cobra/test_if_simple.cobra", "6");
mk_fail_test!(cobra_test_arith_err, "cobra/arth_num_err.cobra", "arithmetic expected a number");
mk_test!(cobra_test_not_true, "cobra/test_not_true.cobra", "false");
mk_test!(cobra_test_print_2, "cobra/test_print_2.cobra", "2\n4\n4");
mk_test!(cobra_test_print_simple, "cobra/test_print_simple.cobra", "5\n5");

// boa tests:
mk_test!(boa_test_num1, "boa/test_num.boa", "483");
mk_test!(boa_test_num2, "boa/test_num_2.boa", "12");
mk_test!(boa_test_let_simple, "boa/test_let_simple.boa", "1");
mk_test!(boa_test_many_var, "boa/test_many_var.boa", "2");
mk_test!(boa_test_let_var_chain, "boa/test_let_var_chain.boa", "13");
mk_test!(boa_test_prim_simple, "boa/test_prim_simple.boa", "13");
mk_test!(boa_test_prim_chain, "boa/test_prim_chain.boa", "2");
mk_test!(boa_test_var_simple, "boa/test_var_simple.boa", "5");
mk_test!(boa_test_var_add, "boa/test_var_add.boa", "3");
mk_test!(boa_test_multiple_bindings, "boa/test_multiple_bindings.boa", "20");

// These should print "if expected a boolean" to console
mk_fail_test!(boa_test_if_simple, "boa/test_if_simple.boa", "if expected a boolean");
//mk_test!(test_mult_if, "test_mult_if.boa", "55");
//mk_test!(test_if_nested, "test_if_nested.boa","23");
mk_test!(boa_test_add_simple, "boa/test_add_simple.boa","9");
mk_test!(boa_test_sub_simple, "boa/test_sub_simple.boa","-6");
mk_test!(boa_test_prim2_let, "boa/test_prim2_let.boa","19");
mk_test!(boa_test_let_nested, "boa/test_let_nested.boa","2");
mk_test!(boa_test_debug_let, "boa/test_debug_let.boa","3");


// IMPLEMENTATION
fn test_example_file(f: &str, expected_str: &str) -> std::io::Result<()> {
    use std::path::Path;
    let p_name = format!("examples/{}", f);
    let path = Path::new(&p_name);

    let tmp_dir = tempfile::TempDir::new()?;
    let mut w = Vec::new();
    match runner::compile_and_run_file(&path, tmp_dir.path(), &mut w) {
        Ok(()) => {
            let stdout = std::str::from_utf8(&w).unwrap();
            assert_eq!(stdout.trim(), expected_str)
        }
        Err(e) => {
            assert!(false, "Expected {}, got an error: {}", expected_str, e)
        }
    }
    Ok(())
}

fn test_example_fail(f: &str, includes: &str) -> std::io::Result<()> {
    use std::path::Path;
    let p_name = format!("examples/{}", f);
    let path = Path::new(&p_name);

    let tmp_dir = tempfile::TempDir::new()?;
    let mut w_run = Vec::new();
    match runner::compile_and_run_file(
        &Path::new(&format!("examples/{}", f)),
        tmp_dir.path(),
        &mut w_run,
    ) {
        Ok(()) => {
            let stdout = std::str::from_utf8(&w_run).unwrap();
            assert!(false, "Expected a failure but got: {}", stdout.trim())
        }
        Err(e) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains(includes),
                "Expected error message to include the string \"{}\" but got the error: {}",
                includes,
                msg
            )
        }
    }
    Ok(())
}
