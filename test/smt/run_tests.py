#!/usr/bin/env python3

import os
import re
import subprocess
import sys
import hashlib
import shutil


mydir = os.path.dirname(__file__)
os.chdir(mydir)
sys.path.insert(0, os.path.join(mydir, '..'))

from sailtest import *

sail_dir = get_sail_dir()
sail = get_sail()

skip_tests = {
    'assembly_mapping_sat': { 'z3', 'cvc4' }, # This test using unsupported CVC4 features
    'arith_unsat': { 'z3', 'cvc4' },
    'arith_LFL_unsat' : { 'z3', 'cvc4' },
    'store_load_sat' : { 'z3', 'cvc4' },
    'load_store_dep_sat' : { 'z3', 'cvc4' },
    'store_load_scattered_sat' : { 'z3', 'cvc4' },
    'mem_builtins_unsat' : { 'z3', 'cvc4' },
    'arith_FFL_3_unsat' : { 'cvc4' },
    'arith_LCBL_unsat' : { 'cvc4' },
    'arith_LC32L_3_unsat' : { 'cvc4' },
    'arith_FFL_5_unsat' : { 'cvc4' },
    # Not $property fixtures, have their own tests below (test_smt_transition*).
    'transition_step' : { 'z3', 'cvc4' },
    'transition_match' : { 'z3', 'cvc4' },
}

print("Sail is {}".format(sail))
print("Sail dir is {}".format(sail_dir))

def test_smt(name, solver, sail_opts):
    banner('Testing SMT: {}'.format(name))
    results = Results(name)
    for filenames in chunks(os.listdir('.'), parallel()):
        tests = {}
        for filename in filenames:
            basename = os.path.splitext(os.path.basename(filename))[0]
            basename = basename.replace('.', '_')
            if basename in skip_tests:
                if name in skip_tests[basename]:
                    print_skip(filename)
                    continue
            tests[filename] = os.fork()
            if tests[filename] == 0:
                step('\'{}\' {} -smt {} -o {}'.format(sail, sail_opts, filename, basename))
                step('timeout 30s {} {}_prop.smt2 1> {}.out'.format(solver, basename, basename))
                if re.match(r'.+\.sat\.sail$', filename):
                    step('grep -q ^sat$ {}.out'.format(basename))
                else:
                    step('grep -q ^unsat$ {}.out'.format(basename))
                print_ok(filename)
                sys.exit()
        results.collect(tests)
    return results.finish()
    return collect_results(name, tests)

def z3_check(smt2, extra):
    result = subprocess.run(['z3', '-in'], input=smt2 + '\n' + extra + '\n(check-sat)\n', capture_output=True, text=True)
    return result.stdout.strip()

def test_smt_transition():
    # transition_step.sail has no branches and no possible overflow/match
    # failure - a straight-line register write. Checks the define-fun's
    # shape (no wrapper functions, no query, no quantifier) and its semantics
    # (it genuinely forces R1_next = x, R2_next = 0x00 and every side
    # condition false, not just that the text parses).
    banner('Testing SMT: -smt_transition')
    results = Results('smt_transition')
    test = 'transition_step'

    step('\'{}\' -smt -smt_transition step {}.sail -o {}'.format(sail, test, test))

    with open('{}_step.smt2'.format(test)) as f:
        smt2 = f.read()

    checks = {
        'one_define_fun_named_step': smt2.count('(define-fun |step| ') == 1,
        'no_assert': '(assert' not in smt2,
        'no_check_sat': '(check-sat)' not in smt2,
        'no_quantifiers': 'exists' not in smt2 and 'forall' not in smt2,
        'no_extra_datatypes': smt2.count('declare-datatypes') == 3,  # Unit, Bits, Zexception only
        'register_params_present': '(|R1| (_ BitVec 16))' in smt2 and '(|R2| (_ BitVec 8))' in smt2,
        'argument_param_present': '(|x| (_ BitVec 16))' in smt2,
        'next_params_present': '(|R1_next| (_ BitVec 16))' in smt2 and '(|R2_next| (_ BitVec 8))' in smt2,
        'side_condition_params_present': '(|overflow| Bool)' in smt2 and '(|assertion_failure| Bool)' in smt2 and '(|match_failure| Bool)' in smt2,
        'correct_instantiation_is_sat': z3_check(smt2, '(assert (step #x0000 #x00 #x1234 #x1234 #x00 false false false))') == 'sat',
        'wrong_instantiation_is_unsat': z3_check(smt2, '(assert (step #x0000 #x00 #x1234 #x0000 #x00 false false false))') == 'unsat',
        # Side conditions are kept as parameters even though this function
        # cannot raise them, so each must be pinned to false.
        'impossible_overflow_is_unsat': z3_check(smt2, '(assert (step #x0000 #x00 #x1234 #x1234 #x00 true false false))') == 'unsat',
        'impossible_assertion_failure_is_unsat': z3_check(smt2, '(assert (step #x0000 #x00 #x1234 #x1234 #x00 false true false))') == 'unsat',
        'impossible_match_failure_is_unsat': z3_check(smt2, '(assert (step #x0000 #x00 #x1234 #x1234 #x00 false false true))') == 'unsat',
        'negated_relation_over_free_state_is_unsat': z3_check(
            smt2,
            '(declare-const r1 (_ BitVec 16)) (declare-const r2 (_ BitVec 8)) (declare-const x (_ BitVec 16))'
            ' (declare-const r1n (_ BitVec 16)) (declare-const r2n (_ BitVec 8))'
            ' (declare-const ov Bool) (declare-const af Bool) (declare-const mf Bool)'
            ' (assert (step r1 r2 x r1n r2n ov af mf))'
            ' (assert (not (and (= r1n x) (= r2n #x00) (not ov) (not af) (not mf))))'
        )
        == 'unsat',
    }

    for check, ok in checks.items():
        if ok:
            results.passes += 1
            results.xml += '    <testcase name="{}"/>\n'.format(check)
            print_ok(check)
        else:
            results._add_failure(check, 'check failed')
            print('{}Failed{}: {}'.format(color.FAIL, color.END, check))

    return results.finish()

def test_smt_transition_match_failure():
    # transition_match.sail's match is non-exhaustive: exercises the
    # match_failure parameter, which used to be computed and then silently
    # discarded (no query/assert in transition mode ever referenced it)
    # unless it's explicitly given a named parameter.
    banner('Testing SMT: -smt_transition match_failure side condition')
    results = Results('smt_transition_match_failure')
    test = 'transition_match'

    step('\'{}\' -smt -smt_transition step {}.sail -o {}'.format(sail, test, test))

    with open('{}_step.smt2'.format(test)) as f:
        smt2 = f.read()

    checks = {
        'match_failure_param_present': '(|match_failure| Bool)' in smt2,
        'overflow_and_assertion_params_present': '(|overflow| Bool)' in smt2 and '(|assertion_failure| Bool)' in smt2,
        'impossible_overflow_is_unsat': z3_check(smt2, '(assert (step #b00 #b00 #b01 true false false))') == 'unsat',
        'impossible_assertion_failure_is_unsat': z3_check(smt2, '(assert (step #b00 #b00 #b01 false true false))') == 'unsat',
        'no_assert_no_check_sat': '(assert' not in smt2 and '(check-sat)' not in smt2,
        'no_quantifiers': 'exists' not in smt2 and 'forall' not in smt2,
        # idx=0b00 -> R1_next=0b01, match_failure=false
        'case_00_is_sat': z3_check(smt2, '(assert (step #b00 #b00 #b01 false false false))') == 'sat',
        'case_00_wrong_result_is_unsat': z3_check(smt2, '(assert (step #b00 #b00 #b10 false false false))') == 'unsat',
        # idx=0b10 matches neither arm -> match_failure must be true
        'unmatched_case_forces_match_failure': z3_check(smt2, '(assert (step #b00 #b10 #b10 false false false))') == 'unsat',
        'unmatched_case_with_match_failure_true_is_sat': z3_check(smt2, '(assert (step #b00 #b10 #b10 false false true))') == 'sat',
    }

    for check, ok in checks.items():
        if ok:
            results.passes += 1
            results.xml += '    <testcase name="{}"/>\n'.format(check)
            print_ok(check)
        else:
            results._add_failure(check, 'check failed')
            print('{}Failed{}: {}'.format(color.FAIL, color.END, check))

    return results.finish()

xml = '<testsuites>\n'
xml += test_smt_transition()
xml += test_smt_transition_match_failure()

if shutil.which('cvc4') is not None:
    xml += test_smt('cvc4', 'cvc4 --lang=smt2.6', '')
else:
    print('{}Cannot find SMT solver cvc4 skipping tests{}'.format(color.WARNING, color.END))

if shutil.which('z3') is not None:
    xml += test_smt('z3', 'z3', '')
else:
    print('{}Cannot find SMT solver z3 skipping tests{}'.format(color.WARNING, color.END))

xml += '</testsuites>\n'

output = open('tests.xml', 'w')
output.write(xml)
output.close()

