from z3 import *
from itertools import product
import matplotlib.pyplot as plt
import time
import tracemalloc
import heapq


class FormulaHeap:
    """Keeps formulas sorted by string length (longest first)."""
    def __init__(self, formulas=None):
        self._heap = []
        for f in (formulas or []):
            self.push(f)

    def push(self, formula):
        heapq.heappush(self._heap, (-len(str(formula)), id(formula), formula))

    def __iter__(self):
        return (f for _, _, f in sorted(self._heap))

    def __len__(self):
        return len(self._heap)

    def __repr__(self):
        return str(list(self))

    def __getitem__(self, idx):
        return list(self)[idx]

    def copy(self):
        new = FormulaHeap()
        new._heap = self._heap[:]
        return new

    def to_list(self):
        return list(self)

    def slice_except(self, idx):
        lst = list(self)
        target = lst[idx]
        new = FormulaHeap()
        new._heap = [item for item in self._heap if item[2] is not target]
        heapq.heapify(new._heap)
        return new

    def plus(self, *formulas):
        new = self.copy()
        for f in formulas:
            new.push(f)
        return new


class sequent:
    def __init__(self, lhs, rhs):
        self.lhs = lhs if isinstance(lhs, FormulaHeap) else FormulaHeap(lhs)
        self.rhs = rhs if isinstance(rhs, FormulaHeap) else FormulaHeap(rhs)

    def __repr__(self):
        return f"{list(self.lhs)} ⊢ {list(self.rhs)}"


def nextRule(operator, side):
    print("next rule is: ", operator, side)

def collect_constants(formula):
    consts = set()
    def visit(f):
        if is_const(f) and f.decl().kind() != Z3_OP_UNINTERPRETED:
            return
        if is_const(f):
            consts.add(f)
        elif is_app(f):
            for arg in f.children():
                visit(arg)
        elif is_quantifier(f):
            visit(f.body())
    visit(formula)
    return consts

fresh_counter = 0
def fresh_const():
    global fresh_counter
    name = f"c_{fresh_counter}"
    fresh_counter += 1
    return Bool(name)

branchesMade = 0
steps_taken = 0

def solve(seq):
    global branchesMade, steps_taken
    rule_applied = False
    branchesMade += 1
    seq_branches = [seq]
    while len(seq_branches) >= 1:
        seq_current = seq_branches.pop()
        #PRIORITY LEVEL 1
        for formula in seq_current.lhs:
            if is_false(formula):
                rule_applied = True
        for formula in seq_current.rhs:
            if is_true(formula):
                rule_applied = True
        for formula_r in seq_current.rhs:
            for formula_l in seq_current.lhs:
                if formula_r == formula_l:
                    rule_applied = True
        if rule_applied == True:
            rule_applied = False
            continue
        #PRIORITY LEVEL 2
        for i, formula in enumerate(seq_current.rhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "=>":
                left = formula.arg(0)
                right = formula.arg(1)
                new_rhs = seq_current.rhs.slice_except(i).plus(right)
                new_lhs = seq_current.lhs.plus(left)
                new_seq = sequent(new_lhs, new_rhs)
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.lhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "and":
                f1 = formula.arg(0)
                f2 = formula.arg(1)
                new_lhs = seq_current.lhs.slice_except(i).plus(f1, f2)
                new_seq = sequent(new_lhs, seq_current.rhs)
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.rhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "or":
                f1 = formula.arg(0)
                f2 = formula.arg(1)
                new_rhs = seq_current.rhs.slice_except(i).plus(f1, f2)
                new_seq = sequent(seq_current.lhs, new_rhs)
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.lhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "not":
                f1 = formula.arg(0)
                new_lhs = seq_current.lhs.slice_except(i)
                new_seq = sequent(new_lhs, seq_current.rhs.plus(f1))
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.rhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "not":
                f1 = formula.arg(0)
                new_rhs = seq_current.rhs.slice_except(i)
                new_seq = sequent(seq_current.lhs.plus(f1), new_rhs)
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.rhs):
            if not is_quantifier(formula):
                continue
            if formula.is_forall():
                variableCount = formula.num_vars()
                body = formula.body()
                fresh_vars = [fresh_const() for _ in range(variableCount)]
                instantiated = substitute_vars(body, *reversed(fresh_vars))
                new_rhs = seq_current.rhs.slice_except(i).plus(instantiated)
                new_seq = sequent(seq_current.lhs, new_rhs)
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.lhs):
            if not is_quantifier(formula):
                continue
            if formula.is_exists():
                variableCount = formula.num_vars()
                body = formula.body()
                fresh_vars = [fresh_const() for _ in range(variableCount)]
                instantiated = substitute_vars(body, *reversed(fresh_vars))
                new_lhs = seq_current.lhs.slice_except(i).plus(instantiated)
                new_seq = sequent(new_lhs, seq_current.rhs)
                seq_branches.append(new_seq)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        #PRIORITY LEVEL 3
        for i, formula in enumerate(seq_current.lhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "or":
                f0 = formula.arg(0)
                f1 = formula.arg(1)
                base_lhs = seq_current.lhs.slice_except(i)
                new_seq1 = sequent(base_lhs.plus(f0), seq_current.rhs)
                new_seq2 = sequent(base_lhs.plus(f1), seq_current.rhs)
                seq_branches.append(new_seq1)
                seq_branches.append(new_seq2)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.rhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "and":
                f0 = formula.arg(0)
                f1 = formula.arg(1)
                base_rhs = seq_current.rhs.slice_except(i)
                new_seq1 = sequent(seq_current.lhs, base_rhs.plus(f0))
                new_seq2 = sequent(seq_current.lhs, base_rhs.plus(f1))
                seq_branches.append(new_seq1)
                seq_branches.append(new_seq2)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.lhs):
            if not is_app(formula):
                continue
            if formula.decl().name() == "=>":
                f0 = formula.arg(0)
                f1 = formula.arg(1)
                base_lhs = seq_current.lhs.slice_except(i)
                new_seq1 = sequent(base_lhs, seq_current.rhs.plus(f0))
                new_seq2 = sequent(base_lhs.plus(f1), seq_current.rhs)
                seq_branches.append(new_seq1)
                seq_branches.append(new_seq2)
                steps_taken += 1
                rule_applied = True
                break
        if rule_applied == True:
            rule_applied = False
            continue
        #PRIORITY LEVEL 4
        for i, formula in enumerate(seq_current.rhs):
            if not is_quantifier(formula):
                continue
            if formula.is_exists():
                variables = set()
                for f in seq_current.lhs:
                    variables.update(collect_constants(f))
                for f in seq_current.rhs:
                    variables.update(collect_constants(f))
                variables = list(variables)
                num_vars = formula.num_vars()
                if len(variables) < num_vars:
                    needed = num_vars - len(variables)
                    for _ in range(needed):
                        variables.append(fresh_const())
                all_combos = list(product(variables, repeat=num_vars))
                for combo in all_combos:
                    instantiated = substitute_vars(formula.body(), *reversed(combo))
                    new_rhs = seq_current.rhs.slice_except(i).plus(instantiated)
                    new_seq = sequent(seq_current.lhs, new_rhs)
                    if solve(new_seq) == True:
                        seq_branches.append(new_seq)
                        steps_taken += 1
                        rule_applied = True
                        break
            if rule_applied == True:
                break
        if rule_applied == True:
            rule_applied = False
            continue
        for i, formula in enumerate(seq_current.lhs):
            if not is_quantifier(formula):
                continue
            if formula.is_forall():
                variables = set()
                for f in seq_current.lhs:
                    variables.update(collect_constants(f))
                for f in seq_current.rhs:
                    variables.update(collect_constants(f))
                variables = list(variables)
                num_vars = formula.num_vars()
                if len(variables) < num_vars:
                    needed = num_vars - len(variables)
                    for _ in range(needed):
                        variables.append(fresh_const())
                all_combos = list(product(variables, repeat=num_vars))
                for combo in all_combos:
                    instantiated = substitute_vars(formula.body(), *reversed(combo))
                    new_lhs = seq_current.lhs.slice_except(i).plus(instantiated)
                    new_seq = sequent(new_lhs, seq_current.rhs)
                    if solve(new_seq) == True:
                        seq_branches.append(new_seq)
                        steps_taken += 1
                        rule_applied = True
                        break
            if rule_applied == True:
                break
        if rule_applied == True:
            rule_applied = False
            continue
        return False
    return True

def run_tests(file_path):
    global steps_taken

    total = 0
    correct = 0
    cumulative_steps = []
    cumulative_times = []
    overall_start = time.time()

    with open(file_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue

            try:
                total += 1
                print(f"test {total}")
                formula_str, expected_str = line.split("|")
                formula_str = formula_str.strip()
                expected_str = expected_str.strip()

                expected = True if expected_str == "True" else False

                parsed = parse_smt2_string(formula_str)[0]
                seq = sequent([], [parsed])
                result = solve(seq)

                if result == expected:
                    print(f"✅ Correct: {formula_str}")
                    correct += 1
                else:
                    print(f"❌ Wrong: {formula_str} | Expected: {expected}, Got: {result}")

            except Exception as e:
                print(f"⚠️ Error processing line: {line}")
                print(e)

            cumulative_steps.append(steps_taken)
            cumulative_times.append(round(time.time() - overall_start, 6))

    print(f"\nFinal Score: {correct}/{total} correct")
    return cumulative_steps, cumulative_times


# main
tracemalloc.start()
start = time.time()

cumulative_steps, cumulative_times = run_tests("tests.txt")

end = time.time()
_, peak_memory = tracemalloc.get_traced_memory()
tracemalloc.stop()

print(f"Time taken: {end - start:.4f} seconds")
print(f"Branches made: {branchesMade}")
print(f"\nCumulative steps per test: {cumulative_steps}")
print(f"\nCumulative time per test (seconds): {cumulative_times}")
print(f"\nPeak memory used: {peak_memory} bytes")