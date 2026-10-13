import sys
import time
import csv
from pathlib import Path
from pysat.solvers import Cadical195
from pysat.pb import PBEnc, EncType

def generate_variables(m, n, c):
    X = [[i + 1 + j * n for i in range(n)] for j in range(m)]
    W = [[X[-1][-1] + i + 1 + j * n for i in range(n)] for j in range(m)]
    R = [[W[-1][-1] + i + 1 + j * n for i in range(n)] for j in range(2 * m)] # dùng để tạo AMO sequential counter cho X và W
    S = [[R[-1][-1] + i + 1 + j * n for i in range(n)] for j in range(c)]
    T = [[S[-1][-1] + i + 1 + j * n for i in range(n)] for j in range(c)] # dùng để tạo AMO sequential counter cho S
    A = [[T[-1][-1] + i + 1 + j * n for i in range(n)] for j in range(c)]
    return X, W, R, S, T, A

def AMO_sequential(clauses, variables, aux_vars):
    for i in range( len(variables)-1):
        clauses.append([-variables[i], aux_vars[i]])
    for i in range( len(aux_vars)-1):
        clauses.append([-aux_vars[i], aux_vars[i+1]])
    for i in range( len(aux_vars)-1):
        clauses.append([-aux_vars[i], -variables[i+1]])

def setup(clause, m, n, c, X, W, R, S, T, A, Ti, relation, P, UB):
    # 1 - Each task can only be assigned to one machine at a time step
    for i in range(n):
        #clause.append([X[j][i] for j in range(m)] + [W[j][i] for j in range(m)])
        #AMO_sequential(clause, [X[j][i] for j in range(m)] + [W[j][i] for j in range(m - 1, -1, -1)], [R[j][i] for j in range( 2 * m-1)])
        clause.append([-X[0][i], R[0][i]])  
        clause.append([-R[0][i], X[0][i]]) #cse-1
        for k in range(1, 2 * m - 1):
            clause.append([R[k][i], -R[k - 1][i]]) #cse-2
            if k < m:
                clause.append([-X[k][i], R[k][i]]) #cse-3a
                clause.append([-X[k][i], -R[k - 1][i]]) #cse-4a
                clause.append([-R[k][i], R[k - 1][i], X[k][i]]) #cse-5a
            if k >= m:
                clause.append([-W[2 * m - k - 1][i], R[k][i]]) #cse-3b
                clause.append([-W[2 * m - k - 1][i], -R[k - 1][i]]) #cse-4b
                clause.append([-R[k][i], R[k - 1][i], W[2 * m - k - 1][i]]) #cse-5b

        clause.append([-W[0][i], -R[2 * m - 2][i]]) #cse-5c
        clause.append([W[0][i], R[2 * m - 2][i]]) #cse-5d
            
    # 2 - Precedence constraints: machine gates
    for (i, j) in relation:
       for k in range(1, 2 * m):
            if k < m:
               clause.append([-X[k][i], -R[k - 1][j]]) #cse-6a
            if k >= m:
                clause.append([-W[2 * m - k - 1][i], -R[k - 1][j]]) #cse-6b

    # 3 - Each task can only be started on one time step
    for i in range(n):
        #clause.append([S[t][i] for t in range(0, c - Ti[i] + 1)])
        #AMO_sequential(clause, [S[t][i] for t in range(0, c - Ti[i] + 1)],[T[t][i] for t in range( c - Ti[i])])

        clause.append([-T[0][i], S[0][i]])
        clause.append([-S[0][i], T[0][i]]) #cse - 7
        last_time = c - Ti[i] + 1
        for t in range(1, last_time - 1):
            clause.append([T[t][i], -T[t - 1][i]])
            clause.append([-S[t][i], T[t][i]])
            clause.append([-S[t][i], -T[t - 1][i]])
            clause.append([-T[t][i], T[t - 1][i], S[t][i]])

        clause.append([-S[last_time - 1][i], -T[last_time - 2][i]])
        clause.append([S[last_time - 1][i], T[last_time - 2][i]])


    # 4 - Each task can only be assigned at time steps that are within its processing time
    for i in range(n):
        for t0 in range(0, c):
            for t in range(t0, min(t0 + Ti[i], c)):
                clause.append([-S[t0][i], A[t][i]])

    # 5a - Define same machine
    SM = [[A[-1][-1] + 1 + i + j * n for i in range(n)] for j in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                for k in range(m):
                    clause.append([-X[k][i], -X[k][j], SM[i][j]])
                    clause.append([-W[k][i], -W[k][j], SM[i][j]])
                    clause.append([-X[k][i], -W[k][j], SM[i][j]])
                    clause.append([-X[k][j], -W[k][i], SM[i][j]])
                    for k1 in range(m):
                        if k1 != k:
                            clause.append([-SM[i][j], -X[k][i], -X[k1][j]])
                            clause.append([-SM[i][j], -W[k][i], -W[k1][j]])
                            clause.append([-SM[i][j], -X[k][i], -W[k1][j]])
                            clause.append([-SM[i][j], -X[k1][j], -W[k][i]])

    # 5 - Overlapping constraints: if task i is assigned to machine s at time t, then task j cannot be assigned to machine s at time t
    for t in range(c):
        for s in range(m):
            for i in range(n):
                for j in range(n):
                    if i != j:
                        clause.append([-A[t][j], -A[t][i], -SM[i][j]])
                        
    # 6 - If task i is assigned to in gate, it cannot be assigned after task j in out gate at same station
    for i in range(n):
        for j in range(n):
            if i != j:
                for k in range(m):
                    for t in range(c):
                        for t1 in range(t):
                            clause.append([-S[t][i], -S[t1][j], -X[k][i], -W[k][j]])

    # 7 - Precedence constraints: if task i is assigned to a machine at time t, then task j cannot be assigned before time t + Ti[i] - 1
    # task i and j must be assigned to the same machine
    for (i, j) in relation:
        for k in range(m):
            left = Ti[i] - 1
            right = c - Ti[j]
            clause.append([-SM[i][j], -T[left][j]])
            for t in range(left + 1, right):
                t_i = t - Ti[i] + 1
                clause.append([-SM[i][j], -S[t_i][i], -T[t][j]])

            for t in range(max(0, right - Ti[i] + 1), c - Ti[i] + 1):
                clause.append([-SM[i][j], -S[t][i], - T[c - Ti[j] - 1][j]])

    # 8 - Task cannot be assigned over fesible time steps
    for i in range(n):
        for t in range(c - Ti[i] + 1, c):
            clause.append([-S[t][i]])

    # 9 - Power consumption constraint
    count = SM[-1][-1] + 1
    for i in range(c):
        lits, weights = [], []
        for j in range(n):
            lits.append(A[i][j])
            weights.append(P[j])
        pb_constraint = PBEnc.leq(
            lits=lits, weights=weights, bound=UB, top_id=count, encoding=EncType.binmerge
        )            
        for clauses in pb_constraint:
            clause.append(clauses)
        if pb_constraint.nv > count:
            count = pb_constraint.nv + 1

def read_file(file_name):
    W, relation, times = [], set(), []
    with open(f"task_power/{file_name}.txt") as f:
        for line in f:
            W.append(int(line.strip()))
    with open(f"data/{file_name}.IN2") as f:
        lines = f.readlines()
    n = int(lines[0])
    x_time_count = 0
    for line in lines[1:]:
        line = line.strip()
        if not line:
            continue
        if x_time_count < n:
            times.append(int(line))
            x_time_count += 1
        else:
            pair = tuple(map(int, line.split(',')))
            if pair == (-1, -1):
                break
            relation.add((pair[0] - 1, pair[1] - 1))
    return n, W, relation, times

def get_values(model, m, n, c, P, X, W, S, A, Ti):
    schedule = [[0 for _ in range(c)] for _ in range(m)]
    constraints = []
    val = lambda var_id: model[abs(var_id) - 1] if model[abs(var_id) - 1] > 0 else model[abs(var_id) - 1]
    
    X = [[val(X[k][j]) for j in range(n)] for k in range(m)]
    W = [[val(W[k][j]) for j in range(n)] for k in range(m)]
    S = [[val(S[t][j]) for j in range(n)] for t in range(c)]
    A = [[val(A[t][j]) for j in range(n)] for t in range(c)]

    makespan = 0
    for i in range(c):
        for k in range(m):
            for j in range(n):
                if S[i][j] > 0 and (X[k][j] > 0 or W[k][j] > 0):
                    constraints.append(S[i][j])
                    for t in range(i, min(c, i + Ti[j])):
                        if X[k][j] > 0:
                            schedule[k][t] = P[j]
                        if W[k][j] > 0:
                            schedule[k][t] = -P[j]
                        constraints.append(-A[t][j])
                        makespan = max(makespan, t + 1)
    
    return schedule, makespan, constraints

def log_to_csv(name, n, m, c, makespan, sol, count, lenthclause, exec_time, status):
    """Add or update one CSV row for a unique filename/n/m/c combination."""
    log_file = Path("Avg_peak/Output/ss.csv")
    header = [
        "Filename", "Tasks", "Machines", "Cycle Time", "Makespan",
        "Solutions times", "Variable Count", "Clause Length",
        "Execution Time", "Status",
    ]
    new_row = [name, n, m, c, makespan, sol, count, lenthclause, f"{exec_time:.2f}", status]
    rows = []

    if log_file.exists() and log_file.stat().st_size > 0:
        with open(log_file, mode="r", newline="") as file:
            reader = csv.reader(file)
            next(reader, None)
            rows = list(reader)

    key = [str(name), str(n), str(m), str(c)]
    rows = [row for row in rows if row[:4] != key]
    rows.append(new_row)

    with open(log_file, mode="w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(header)
        writer.writerows(rows)

def optimize(n, m, c, LB, name, P, relation, Ti, peak):
    start_time = time.time()
    X, W, R, S, T, A = generate_variables(m, n, c)
    P_sorted = sorted(P, reverse=True)
    clauses = []
    setup(clauses, m, n, c, X, W, R, S, T, A, Ti, relation, P, peak)
    solver = Cadical195()
    for clause in clauses:
        solver.add_clause(clause)
        
    result = solver.solve()
    sol = 0
    if result:
        model = solver.get_model()
        schedule, makespan, new_constraints = get_values(model, m, n, c, P, X, W, S, A, Ti)
        count = len(solver.get_model())
        lenthclause = len(model)
        
        # GHI NHẬN KẾT QUẢ BAN ĐẦU
        log_to_csv(name, n, m, c, makespan, sol, count, lenthclause, time.time() - start_time, "FEASIBLE")
        print(f"[{name}] Initial makespan: {makespan}")

        while True:
            sol += 1
            print(f"[{name}] Iteration {sol}: Current makespan: {makespan}")
            if makespan - 1 < LB:
                print("Reached lower bound. Optimal solution found.")
                log_to_csv(name, n, m, c, makespan, sol, count, lenthclause, time.time() - start_time, "OPTIMAL")
                return 0
            for i in range(n):
                if makespan - Ti[i] - 1 < 0:
                    print("Optimal solution found.")
                    return 0
                solver.add_clause([T[makespan - Ti[i] - 1][i]])

            result = solver.solve()
            if result:
                model = solver.get_model()
                schedule, new_makespan, new_constraints = get_values(model, m, n, c, P, X, W, S, A, Ti)
                if new_makespan < makespan:
                    makespan = new_makespan
                    # GHI ĐÈ KẾT QUẢ TỐT HƠN NGAY LẬP TỨC
                    log_to_csv(name, n, m, c, makespan, sol, count, lenthclause, time.time() - start_time, "IMPROVED")
                    print(f"[{name}] New Makespan: {makespan}")
            else:
                print(f"[{name}] Optimal Makespan: {makespan}")
                log_to_csv(name, n, m, c, makespan, sol, count, lenthclause, time.time() - start_time, "OPTIMAL")
                return 0
    else:
        log_to_csv(name, n, m, c, 0, 0, 0, len(clauses), time.time() - start_time, "UNSAT")
        return 0

if __name__ == "__main__":
    if len(sys.argv) < 4:
        sys.exit(1)
    name = sys.argv[1]
    m = int(sys.argv[2])
    c = int(sys.argv[3])
    
    n, P, relation, Ti = read_file(name)
    P_Sorted = sorted(P, reverse=True)
    Q_max = sum(P_Sorted[i] for i in range(m))
    Q_min = max(P)
    Q_avg = int(sum(P) * m / n) + 1
    peak = (Q_avg + Q_min) // 2
    LB = max(max(Ti), int(sum(Ti) / m) + 1, int(sum([P[i] * Ti[i] for i in range(n)]) / peak) + 1)
    UB = max(LB, int(2 * sum(Ti) / m) + 1)
    optimize(n, m, UB, LB, name, P, relation, Ti, peak)