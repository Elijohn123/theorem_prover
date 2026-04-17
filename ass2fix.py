from z3 import *
import traceback
import time
import tracemalloc

#helper functions
class sequent:
    def __init__(self, lhs: list, rhs: list):
        self.lhs = lhs
        self.rhs = rhs
    def __repr__(self):
        return f"{self.lhs} ⊢ {self.rhs}"

def is_relation(f):
    return is_app_of(f, Z3_OP_UNINTERPRETED) or (is_func_decl(f) and f.arity() >= 0)

g_time = 0
steps_taken = 0  # global steps counter

fresh_time = {}
fresh_counter = 0
def fresh_const():
    global g_time, fresh_time, fresh_counter
    fresh_counter += 1
    name = f"c_{fresh_counter}"
    fresh_time[name] = g_time
    return Bool(name)

t_time = {}
t_counter = 0
def t_const():
    global g_time, t_time, t_counter
    t_counter += 1
    name = f"t_{t_counter}"
    t_time[name] = g_time 
    return Bool(name)

def get_formula_name(f):
    if is_app(f):
        return f.decl().name()
    return None

def match_arguments(f1, f2):
    pass

t_counter_dict = {}

def args_match(args1, args2):
    global t_time, fresh_time
    global t_counter_dict
    if len(args1) != len(args2):
        return False
    unified = []
    for a, b in zip(args1, args2):
        sa, sb = str(a), str(b)
        print("matching:", sa, sb) if TEST_MODE else None
        if sa in fresh_time:
            print(f"time of {sa}: ", fresh_time[sa]) if TEST_MODE else None
        if sa in t_time:
            print(f"time of {sa}: ", t_time[sa]) if TEST_MODE else None
        if sb in fresh_time:
            print(f"time of {sb}: ", fresh_time[sb]) if TEST_MODE else None
        if sb in t_time:
            print(f"time of {sb}: ", t_time[sb]) if TEST_MODE else None
        if sa.startswith("t_") and sb.startswith("t_"):
            in_group = False
            for group in unified:
                if sa in group or sb in group:
                    group.add(sa)
                    group.add(sb)
                    in_group = True
                if in_group == True:
                    break
            if in_group == True:
                in_group = False
                continue
            else:
                tempSet = set()
                tempSet.add(sa)
                tempSet.add(sb)
                unified.append(tempSet)
                continue
        if sa.startswith("t_"):
            if fresh_time[sb] > t_time[sa]:
                return False
            in_group = False
            for group in unified:
                if sa in group:
                    for t in group:
                        t_counter_dict[t] = sb
                        in_group = group
            if in_group != False:
                unified.remove(in_group)
                in_group = False
                continue
            if sa not in t_counter_dict:
                t_counter_dict[sa] = sb
            elif t_counter_dict[sa] != sb:
                return False
            continue
        if sb.startswith("t_"):
            if fresh_time[sa] > t_time[sb]:
                return False
            in_group = False
            for group in unified:
                if sb in group:
                    for t in group:
                        t_counter_dict[t] = sa
                        in_group = group
            if in_group != False:
                unified.remove(in_group)
                in_group = False
                continue
            if sb not in t_counter_dict:
                t_counter_dict[sb] = sa
            elif t_counter_dict[sb] != sa:
                return False
            continue
        if sa != sb:
            return False
    return True

def formula_match(f1, f2):
    if f1 == f2:
        return True
    elif is_app(f1) and is_app(f2) and f1.decl() == f2.decl():
        if args_match(f1.children(), f2.children()):
            return True
    return False
    
#PRIORITY LEVEL 1
def apply_identity_rule(sequent):
    for rf in sequent.rhs:
        for rl in sequent.lhs:
            if formula_match(rf, rl) == True:
                print("id rule applied") if TEST_MODE else None
                return True          
    return False

def apply_TR_rule(sequent):
    for formula in sequent.rhs:
        if is_true(formula):
            print("⊤R rule applied") if TEST_MODE else None
            return True

def apply_FL_rule(sequent):
    for formula in sequent.lhs:
        if is_false(formula):
            print("⊥L rule applied") if TEST_MODE else None
            return True

#PRIORITY LEVEL 2
def apply_andL_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.lhs): 
        if is_app(formula) and get_formula_name(formula) == "and":
            f1 = formula.arg(0)
            f2 = formula.arg(1)
            new_lhs = seq.lhs[:i] + seq.lhs[i+1:] + [f1, f2]
            print("∧L rule applied") if TEST_MODE else None
            steps_taken += 1
            return sequent(new_lhs, seq.rhs)
    return False

def apply_orR_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.rhs):
        if is_app(formula) and get_formula_name(formula) == "or":
            f1 = formula.arg(0)
            f2 = formula.arg(1)
            new_rhs = seq.rhs[:i] + seq.rhs[i+1:] + [f1, f2]
            print("∨R rule applied") if TEST_MODE else None
            steps_taken += 1
            return sequent(seq.lhs, new_rhs)
    return False

def apply_implication_R_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.rhs): 
        if is_app(formula) and get_formula_name(formula) == "=>":
            left = formula.arg(0)
            right = formula.arg(1)
            new_rhs = seq.rhs[:i] + seq.rhs[i+1:]
            print("→R rule applied") if TEST_MODE else None
            steps_taken += 1
            return sequent(seq.lhs + [left], new_rhs + [right])
    return False

def apply_negationR_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.rhs):
        if is_app(formula) and get_formula_name(formula) == "not":
            f1 = formula.arg(0)
            new_rhs = seq.rhs[:i] + seq.rhs[i+1:]
            print("¬R rule applied") if TEST_MODE else None
            steps_taken += 1
            return sequent(seq.lhs + [f1], new_rhs)
    return False

def apply_negationL_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.lhs):
        if is_app(formula) and get_formula_name(formula) == "not":
            f1 = formula.arg(0)
            new_lhs = seq.lhs[:i] + seq.lhs[i+1:]
            print("¬L rule applied") if TEST_MODE else None
            steps_taken += 1
            return sequent(new_lhs, seq.rhs + [f1])
    return False

def apply_existsL_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.lhs):
        if is_quantifier(formula) and formula.is_exists():
            variableCount = formula.num_vars()
            body = formula.body()
            fresh_vars = [fresh_const() for _ in range(variableCount)]
            instantiated = substitute_vars(body, *reversed(fresh_vars))
            new_lhs = seq.lhs[:i] + seq.lhs[i+1:] + [instantiated]
            new_seq = sequent(new_lhs, seq.rhs)
            print("∃L rule applied") if TEST_MODE else None
            steps_taken += 1
            return new_seq
    return False

def apply_forallR_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.rhs):
        if is_quantifier(formula) and formula.is_forall():
            variableCount = formula.num_vars()
            body = formula.body()
            fresh_vars = [fresh_const() for _ in range(variableCount)]
            instantiated = substitute_vars(body, *reversed(fresh_vars))
            new_rhs = seq.rhs[:i] + seq.rhs[i+1:] + [instantiated]
            print("∀R rule applied") if TEST_MODE else None
            steps_taken += 1
            return sequent(seq.lhs, new_rhs)
    return False

#PRIORITY LEVEL 3
def apply_andR_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.rhs):
        if is_app(formula) and get_formula_name(formula) == "and":
            f0 = formula.arg(0)
            f1 = formula.arg(1)
            new_rhs1 = seq.rhs[:i] + seq.rhs[i+1:] + [f0]
            new_rhs2 = seq.rhs[:i] + seq.rhs[i+1:] + [f1]
            new_seq1 = sequent(seq.lhs, new_rhs1)
            new_seq2 = sequent(seq.lhs, new_rhs2)
            print("∧R rule applied") if TEST_MODE else None
            steps_taken += 1
            return (new_seq1, new_seq2)
    return False

def apply_orL_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.lhs):
        if is_app(formula) and get_formula_name(formula) == "or":
            f0 = formula.arg(0)
            f1 = formula.arg(1)
            new_lhs1 = seq.lhs[:i] + seq.lhs[i+1:] + [f0]
            new_lhs2 = seq.lhs[:i] + seq.lhs[i+1:] + [f1]
            new_seq1 = sequent(new_lhs1, seq.rhs)
            new_seq2 = sequent(new_lhs2, seq.rhs)
            print("∨L rule applied") if TEST_MODE else None
            steps_taken += 1
            return (new_seq1, new_seq2)
    return False

def apply_implication_L_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.lhs):
        if is_app(formula) and get_formula_name(formula) == "=>":
            f0 = formula.arg(0)
            f1 = formula.arg(1)
            seq1_new_rhs = seq.rhs + [f0]
            seq1_new_lhs = seq.lhs[:i] + seq.lhs[i+1:]
            seq2_new_rhs = seq.rhs
            seq2_new_lhs = seq.lhs[:i] + seq.lhs[i+1:] + [f1]
            new_seq1 = sequent(seq1_new_lhs, seq1_new_rhs)
            new_seq2 = sequent(seq2_new_lhs, seq2_new_rhs)
            print("→L rule applied") if TEST_MODE else None
            steps_taken += 1
            return (new_seq1, new_seq2)
    return False

#PRIORITY LEVEL 4
def apply_forallL_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.lhs):
        if is_quantifier(formula) and formula.is_forall():
            variableCount = formula.num_vars()
            body = formula.body()
            var_to_t = {}
            our_vars = []
            for idx in range(variableCount):
                var_name = formula.var_name(idx)
                if var_name not in var_to_t:
                    var_to_t[var_name] = t_const()
                our_vars.append(var_to_t[var_name])
            instantiated = substitute_vars(body, *reversed(our_vars))
            new_lhs = seq.lhs[:i] + seq.lhs[i+1:] + [instantiated]
            new_seq = sequent(new_lhs, seq.rhs)
            print("∀L rule applied") if TEST_MODE else None
            steps_taken += 1
            return new_seq
    return False

def apply_existsR_rule(seq):
    global steps_taken
    for i, formula in enumerate(seq.rhs):
        if is_quantifier(formula) and formula.is_exists():
            variableCount = formula.num_vars()
            body = formula.body()
            var_to_t = {}
            our_vars = []
            for idx in range(variableCount):
                var_name = formula.var_name(idx)
                if var_name not in var_to_t:
                    var_to_t[var_name] = t_const()
                our_vars.append(var_to_t[var_name])
            instantiated = substitute_vars(body, *reversed(our_vars))
            new_rhs = seq.rhs[:i] + seq.rhs[i+1:] + [instantiated]
            new_seq = sequent(seq.lhs, new_rhs)
            print("∃R rule applied") if TEST_MODE else None
            steps_taken += 1
            return new_seq
    return False

def solve(seq, last_step=0, time=0):
    global g_time
    g_time = time
    print(seq, f"time = {g_time} last_step_priority = {last_step}") if TEST_MODE else None
    while True:
        #PRIORITY 1
        if apply_identity_rule(seq) == True:
            return True
        if apply_TR_rule(seq) == True:
            return True
        if apply_FL_rule(seq) == True:
            return True
        #PRIORITY 2
        temp = apply_andL_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        temp = apply_orR_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        temp = apply_implication_R_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        temp = apply_negationL_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        temp = apply_negationR_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        temp = apply_forallR_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        temp = apply_existsL_rule(seq)
        if temp != False:
            j = 1 if last_step > 2 else 0
            return solve(temp, 2, time + j)
        #PRIORITY 3
        temp = apply_andR_rule(seq)
        if temp != False:
            j = 1 if last_step > 3 else 0
            return solve(temp[0], 3, time) and solve(temp[1], 3, time + j)
        temp = apply_orL_rule(seq)
        if temp != False:
            j = 1 if last_step > 3 else 0
            return solve(temp[0], 3, time) and solve(temp[1], 3, time + j)
        temp = apply_implication_L_rule(seq)
        if temp != False:
            j = 1 if last_step > 3 else 0
            return solve(temp[0], 3, time) and solve(temp[1], 3, time + j)
        #PRIORITY 4
        temp = apply_forallL_rule(seq)
        if temp != False:
            j = 1 if last_step > 4 else 0
            return solve(temp, 4, time + j)
        temp = apply_existsR_rule(seq)
        if temp != False:
            j = 1 if last_step != 4 else 0
            return solve(temp, 4, time + j)
        print("no rules applied") if TEST_MODE else None
        return False 

def run_tests(file_path): 
    global steps_taken

    total = 1
    correct = 1
    cumulative_steps = []
    cumulative_times = []
    overall_start = time.time()

    with open(file_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue

            try:
                formula_str, expected_str = line.split("|")
                formula_str = formula_str.strip()
                expected_str = expected_str.strip()
                expected = True if expected_str == "True" else False

                parsed = parse_smt2_string(formula_str)[0]
                seq = sequent([], [parsed])

                global t_counter_dict, t_counter, fresh_counter
                t_counter_dict = {}
                t_counter = 0
                fresh_counter = 0

                result = solve(seq)

                if result == expected:
                    print(f"test: {total} ✅ Correct: {formula_str}") 
                    correct += 1
                else:
                    print(f"test: {total} ❌ Wrong: {formula_str} | Expected: {expected}, Got: {result}") 
                total += 1

                # record cumulative steps and time after each test
                cumulative_steps.append(steps_taken)
                cumulative_times.append(round(time.time() - overall_start, 6))

            except Exception as e:
                print(f"\ntest: {total}⚠️ Error processing line:") 
                print(f"INPUT: {line}") if TEST_MODE else None
                print(f"ERROR TYPE: {type(e).__name__}") if TEST_MODE else None
                print(f"MESSAGE: {e}") if TEST_MODE else None
                print("TRACEBACK:") if TEST_MODE else None
                traceback.print_exc() if TEST_MODE else None

                total += 1
                cumulative_steps.append(steps_taken)
                cumulative_times.append(round(time.time() - overall_start, 6))

    print(f"\nFinal Score: {correct}/{total} correct")
    return cumulative_steps, cumulative_times


# main
TEST_MODE = False

tracemalloc.start()
start = time.time()

file_path = "tests.txt"
cumulative_steps, cumulative_times = run_tests(file_path)

end = time.time()
_, peak_memory = tracemalloc.get_traced_memory()
tracemalloc.stop()

print(f"Time taken: {end - start:.4f} seconds")
print(f"\nCumulative steps per test: {cumulative_steps}")
print(f"\nCumulative time per test (seconds): {cumulative_times}")
print(f"\nPeak memory used: {peak_memory} bytes")