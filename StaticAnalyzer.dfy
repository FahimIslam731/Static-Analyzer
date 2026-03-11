// ECS 261 Final Project
// StaticAnalyzer.dfy

module StaticAnalyzer {    
    // AST Syntax Definition

    // abstract state of variables, not like the dynamically updated map of variables but is able to track certain aspects of the variables
    // datatype AbsVal = Zero | NonZero | Unknown
    datatype AbsVal = Zero | NonZero | Unknown
    type AbsState = map<string, AbsVal>
    
    // Expression datatype
    datatype Expr =
        | Const(n: int)
        | Var(x: string)
        | Add(e1: Expr, e2: Expr)
        | Sub(e1: Expr, e2: Expr)
        | Mul(e1: Expr, e2: Expr)
        | Div(e1: Expr, e2: Expr)
        | Mod(e1: Expr, e2: Expr) 

    // Statement datatype
    datatype Stmt =
        | Skip
        | Assign(x: string, e: Expr)
        | Seq(s1: Stmt, s2: Stmt)
        | If(cond: Expr, t: Stmt, f: Stmt)

    // Runtime model
    
    // We model the concrete environment as a map with variable names as the keys to their corresponding values as the value.
    // If a variable is missing from the map, it is "uninitialized", and it will cause an error if it accessed (without having been initialized).
    type Env = map<string, int>

    // Runtime errors to detect for.
    datatype RuntimeError =
        | DivByZero
        | UninitializedVar(x: string)
        // out of bounds

    // Result can either be Ok, or a runtime error.
    datatype Result<T> =
        | Ok(v: T)
        | Err(e: RuntimeError)

    // Set/Update a variable
    function Update(env: Env, x: string, v: int): Env
        ensures x in Update(env, x, v)
        ensures Update(env, x, v)[x] == v
    {
        env[x := v]
    }

    // -----------------------------
    // 3) Expression evaluation (runtime)
    // -----------------------------
    function EvalExpr(e: Expr, env: Env): Result<int>
        decreases e
    {
        match e

        // If e is a constant, return Ok()
        case Const(n) => Ok(n)

        // If e is a variable, return ok if exists and RuntimeError if not.
        case Var(x) =>
            if x in env then Ok(env[x]) else Err(UninitializedVar(x))

        // If e is an addition between two expressions, evaluate the addition, checking for errors.
        case Add(a,b) =>
            match EvalExpr(a, env) {
            // if evaluating a returns an error, we propogate the error upwards
            case Err(er) => Err(er)
            // if a is ok, we verify b for any errors.
            case Ok(v1) =>
                match EvalExpr(b, env) {
                // if evaluating a returns an error, we propogate the error upwards
                case Err(er) => Err(er)
                // if b is also ok, we return the value of v1 + v2.
                case Ok(v2) => Ok(v1 + v2)
                }
            }

        // We follow the same process as in addition above, for sub., mult., and div, operations.
        case Sub(a,b) =>
            match EvalExpr(a, env) {
            case Err(er) => Err(er)
            case Ok(v1) =>
                match EvalExpr(b, env) {
                case Err(er) => Err(er)
                case Ok(v2) => Ok(v1 - v2)
                }
            }

        // If e is a multiplication between two expressions, evaluate the expressions, checking for errors.
        case Mul(a,b) =>
            match EvalExpr(a, env) {
            case Err(er) => Err(er)
            case Ok(v1) =>
                match EvalExpr(b, env) {
                case Err(er) => Err(er)
                case Ok(v2) => Ok(v1 * v2)
                }
            }

        // If e is a division between two expressions, evaluate the expressions, checking for errors.
        case Div(a,b) =>
            match EvalExpr(a, env) {
            case Err(er) => Err(er)
            case Ok(v1) =>
                match EvalExpr(b, env) {
                case Err(er) => Err(er)
                case Ok(v2) =>
                    if v2 == 0 then Err(DivByZero) else Ok(v1 / v2)
                }
            }

        case Mod(a,b) =>
            match EvalExpr(a, env) {
            case Err(er) => Err(er)
            case Ok(v1) =>
                match EvalExpr(b, env) {
                case Err(er) => Err(er)
                case Ok(v2) =>
                    if v2 == 0 then Err(DivByZero) else Ok(v1 % v2)
                }
            }
    }

    // Statement execution (runtime)
    function ExecStmt(s: Stmt, env: Env): Result<Env>
        decreases s
    {
        match s
        // If the statement is to skip, we can simply return ok.
        case Skip => Ok(env)
        
        // Assignment of a variable
        case Assign(x, e) =>
            match EvalExpr(e, env) {
                case Err(er) => Err(er)
                case Ok(v) => Ok(Update(env, x, v))
            }
        
        // Two consective statements
        case Seq(s1, s2) =>
            match ExecStmt(s1, env) {
                // check if error is returned
                case Err(er) => Err(er)
                // execute the if statement
                case Ok(env1) => ExecStmt(s2, env1) //Error
            }

        // If statement
        case If(cond, then_statement, else_statement) =>
            // Evaluate the condition, checking for any errors.
            match EvalExpr(cond, env) {
                // check if error is returned
                case Err(er) => Err(er)
                // execute the if statement
                case Ok(vc) => if vc != 0 then ExecStmt(then_statement, env) else ExecStmt(else_statement, env)
            }
    }

    function AbsEval(e: Expr, state: AbsState): AbsVal        
        decreases e
    {
        match e
        case Const(n) => if n == 0 then Zero else NonZero

        case Var(x) => if x in state then state[x] else Unknown

        case Add(a,b) =>
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);
            
            if a_eval == Zero && b_eval == Zero then Zero
            else if a_eval == NonZero && b_eval == Zero then NonZero
            else if a_eval == Zero && b_eval == NonZero then NonZero
            else Unknown

        case Sub(a,b) =>
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);
            
            if a_eval == Zero && b_eval == Zero then Zero
            else if a_eval == NonZero && b_eval == Zero then NonZero
            else if a_eval == Zero && b_eval == NonZero then NonZero
            else Unknown

        case Mul(a,b) =>
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);

            if a_eval == Zero || b_eval == Zero then Zero
            else if a_eval == NonZero && b_eval == NonZero then NonZero
            else Unknown

        case Div(a, b) => 
            if AbsEval(a, state) == Zero && AbsEval(b, state) == NonZero then Zero else Unknown

        case Mod(a, b) => 
            if AbsEval(a, state) == Zero && AbsEval(b, state) == NonZero then Zero else Unknown
    }
    
    function CheckExpr(e: Expr, state: AbsState): bool
        decreases e
    {
        match e

        case Const(n) => true

        case Var(x) => x in state

        case Add(a,b) => CheckExpr(a, state) && CheckExpr(b, state)
        
        case Sub(a,b) => CheckExpr(a, state) && CheckExpr(b, state)
        
        case Mul(a,b) => CheckExpr(a, state) && CheckExpr(b, state)

        case Div(a,b) => CheckExpr(a, state) && CheckExpr(b, state) && AbsEval(b, state) == NonZero

        case Mod(a,b) => CheckExpr(a, state) && CheckExpr(b, state) && AbsEval(b, state) == NonZero
    }

    function JoinVal(a: AbsVal, b: AbsVal): AbsVal
    {
        if a == b then a else Unknown
    }

    function JoinState(s1: AbsState, s2: AbsState): AbsState
    {
        map k | k in s1 && k in s2 :: JoinVal(s1[k], s2[k])
    }

    function AnalyzeStmt(s: Stmt, state: AbsState): (bool, AbsState)
        decreases s
    {
        match s

        case Skip => (true, state)

        case Assign(x, e) =>
            if CheckExpr(e, state)
            then (true, state[x := AbsEval(e, state)])
            else (false, state)
        
        case Seq(s1, s2) =>
            match AnalyzeStmt(s1, state){
                case (false, state_f_s1) => (false, state_f_s1)
                case (true, state_t_s1) => AnalyzeStmt(s2, state_t_s1)
            }

        case If(cond, then_statement, else_statement) =>
            if(CheckExpr(cond, state))
                then match AbsEval(cond, state)
                    case NonZero => AnalyzeStmt(then_statement, state)
                    case Zero => AnalyzeStmt(else_statement, state)
                    case Unknown => match AnalyzeStmt(then_statement, state){
                            case (false, state_f_then) => (false, state_f_then)
                            case (true, state_t_then) =>
                                match AnalyzeStmt(else_statement, state) {
                                    case (false, state_f_else) => (false, state_f_else)
                                    case (true, state_t_else) => (true, JoinState(state_t_then, state_t_else))
                                }
                        }
                else (false, state)            
    }

    // helper predicate for an error function
    predicate IsErr(r: Result){
        match r
        case Ok(_) => false
        case Err(_) => true
    }

    predicate Consistent(st: AbsState, env: Env){
        forall x :: x in st ==>
            x in env &&
            (st[x] == Zero ==> env[x] == 0) &&
            (st[x] == NonZero ==> env[x] != 0)
    }

    lemma AbsNonZeroOkValueNonZero(e: Expr, st: AbsState, env: Env, v: int)
        requires AbsEval(e, st) == NonZero
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        requires EvalExpr(e, env) == Ok(v)
        ensures v != 0
        decreases e
    {
        match e
        
        case Const(n) => {
            assert n != 0;
            assert v == n;
        }

        case Var(n) => {
            assert n in st && n in env;
            assert env[n] != 0;
        }

        case Add(a, b) => {
            var a_eval := AbsEval(a, st);
            var b_eval := AbsEval(b, st);

            assert (a_eval == NonZero && b_eval == Zero) || (a_eval == Zero && b_eval == NonZero);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 + v2;
                    if(a_eval == NonZero){
                        AbsZeroOkValueZero(b, st, env, v2);
                        AbsNonZeroOkValueNonZero(a, st, env, v1);
                        assert v2 == 0;
                    } else{
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsNonZeroOkValueNonZero(b, st, env, v2);
                        assert v1 == 0;
                    }
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Sub(a, b) => {
            var a_eval := AbsEval(a, st);
            var b_eval := AbsEval(b, st);

            assert (a_eval == NonZero && b_eval == Zero) || (a_eval == Zero && b_eval == NonZero);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 - v2;
                    if(a_eval == NonZero){
                        AbsZeroOkValueZero(b, st, env, v2);
                        AbsNonZeroOkValueNonZero(a, st, env, v1);
                        assert v2 == 0;
                    } else{
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsNonZeroOkValueNonZero(b, st, env, v2);
                        assert v1 == 0;
                    }
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Mul(a, b) => {
            var a_eval := AbsEval(a, st);
            var b_eval := AbsEval(b, st);

            assert (a_eval == NonZero && b_eval == NonZero);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 * v2;
                    AbsNonZeroOkValueNonZero(a, st, env, v1);
                    AbsNonZeroOkValueNonZero(b, st, env, v2);
                    assert v1 != 0 && v2 != 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Div(a, b) => assert false;

        case Mod(a, b) => assert false;
    }

    // If AbsEval says "Zero", then any Ok(v) must be v == 0
    lemma AbsZeroOkValueZero(e: Expr, st: AbsState, env: Env, v: int)
        requires AbsEval(e, st) == Zero
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        requires EvalExpr(e, env) == Ok(v)
        ensures v == 0
        decreases e
    {
        match e
        case Const(n) => {
            assert n == 0;
            assert v == 0;
        }

        case Var(x) => {
            assert x in st;
            assert x in env;
            assert st[x] == Zero;
            assert env[x] == 0;
            assert v == env[x];
        }

        case Add(a,b) => {
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 + v2;
                    AbsZeroOkValueZero(a, st, env, v1);
                    AbsZeroOkValueZero(b, st, env, v2);
                    assert v1 == v2 == 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Sub(a,b) => {
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 - v2;
                    AbsZeroOkValueZero(a, st, env, v1);
                    AbsZeroOkValueZero(b, st, env, v2);
                    assert v1 == v2 == 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Mul(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert va == Zero || vb == Zero;

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 * v2;
                    if(va == Zero){
                        AbsZeroOkValueZero(a, st, env, v1);
                        assert v1 == 0;
                    } else {
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v2 == 0;
                    }
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Div(a,b) => {
            assert AbsEval(a, st) == Zero && AbsEval(b, st) == NonZero;

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 / v2;
                    AbsZeroOkValueZero(a, st, env, v1);
                    AbsNonZeroOkValueNonZero(b, st, env, v2);
                    assert v1 == 0;
                    assert v2 != 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Mod(a,b) => {
            assert AbsEval(a, st) == Zero && AbsEval(b, st) == NonZero;

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 % v2;
                    AbsZeroOkValueZero(a, st, env, v1);
                    AbsNonZeroOkValueNonZero(b, st, env, v2);
                    assert v1 == 0;
                    assert v2 != 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }
    }

    lemma CheckTrueEvalValid(e: Expr, st: AbsState, env: Env)
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        ensures !IsErr(EvalExpr(e, env))
        decreases e
    {
        match e
        case Const(n) => {
            assert EvalExpr(Const(n), env) == Ok(n);
        }

        case Var(x) => {
            assert x in st;
            assert x in env; // from Consistent
            assert EvalExpr(Var(x), env) == Ok(env[x]);
        }

        case Add(a,b) => {
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
            match EvalExpr(b, env)
            case Ok(v2) => {
                assert EvalExpr(Add(a,b), env) == Ok(v1 + v2);
            }
            case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Sub(a,b) => {
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
            match EvalExpr(b, env)
            case Ok(v2) => {
                assert EvalExpr(Sub(a,b), env) == Ok(v1 - v2);
            }
            case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Mul(a,b) => {
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
            match EvalExpr(b, env)
            case Ok(v2) => {
                assert EvalExpr(Mul(a,b), env) == Ok(v1 * v2);
            }
            case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Div(a,b) => {
            assert CheckExpr(a, st) && CheckExpr(b, st);
            assert AbsEval(b, st) == NonZero;

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    AbsNonZeroOkValueNonZero(b, st, env, v2);
                    assert v2 != 0;
                    assert EvalExpr(Div(a,b), env) == Ok(v1 / v2);
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        case Mod(a,b) => {
            assert CheckExpr(a, st) && CheckExpr(b, st);
            assert AbsEval(b, st) == NonZero;

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    AbsNonZeroOkValueNonZero(b, st, env, v2);
                    assert v2 != 0;
                    assert EvalExpr(Mod(a,b), env) == Ok(v1 % v2);
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }
    }

    lemma ConsistentJoinLeft(stT: AbsState, stF: AbsState, env: Env)
        requires Consistent(stT, env)
        ensures Consistent(JoinState(stT, stF), env)
    {
        forall k | k in JoinState(stT, stF)
            ensures k in env
            ensures (JoinState(stT, stF)[k] == Zero ==> env[k] == 0)
            ensures (JoinState(stT, stF)[k] == NonZero ==> env[k] != 0)
        {
            // From membership in JoinState:
            assert k in stT && k in stF;
            assert k in env; // from Consistent(stT, env)

            // JoinState[k] = JoinVal(stT[k], stF[k])
            if JoinState(stT, stF)[k] == Zero {
            // then JoinVal(...) == Zero, so stT[k] == stF[k] == Zero
            assert stT[k] == Zero;
            assert env[k] == 0;
            }
            if JoinState(stT, stF)[k] == NonZero {
            assert stT[k] == NonZero;
            assert env[k] != 0;
            }
        }
    }

    lemma ConsistentJoinRight(stT: AbsState, stF: AbsState, env: Env)
        requires Consistent(stF, env)
        ensures Consistent(JoinState(stT, stF), env)
    {
        forall k | k in JoinState(stT, stF)
            ensures k in env
            ensures (JoinState(stT, stF)[k] == Zero ==> env[k] == 0)
            ensures (JoinState(stT, stF)[k] == NonZero ==> env[k] != 0)
        {
            assert k in stT && k in stF;
            assert k in env; // from Consistent(stF, env)

            if JoinState(stT, stF)[k] == Zero {
            assert stF[k] == Zero;
            assert env[k] == 0;
            }
            if JoinState(stT, stF)[k] == NonZero {
            assert stF[k] == NonZero;
            assert env[k] != 0;
            }
        }
    }
    
    lemma AnalyzeTrueExecValid(s: Stmt, st: AbsState, env: Env)
        requires AnalyzeStmt(s, st).0
        requires Consistent(st, env)
        ensures !IsErr(ExecStmt(s, env))
        ensures match ExecStmt(s, env)
            case Ok(envOut) => Consistent(AnalyzeStmt(s, st).1, envOut)
            case Err(_) => true
        decreases s
    {
        match s

        case Skip() => assert ExecStmt(Skip(), env) == Ok(env);

        case Assign(x, e) => {
            assert CheckExpr(e, st);
            CheckTrueEvalValid(e, st, env);

            match EvalExpr(e, env)
            case Ok(v) => {
                var update_env := Update(env, x, v);
                assert ExecStmt(Assign(x, e), env) == Ok(update_env);

                var stOut := AnalyzeStmt(Assign(x, e), st).1;

                assert stOut == st[x := AbsEval(e, st)];

                assert Consistent(stOut, update_env) by 
                {
                    forall y | y in stOut
                        ensures y in update_env
                        ensures (stOut[y] == Zero ==> update_env[y] == 0)
                        ensures (stOut[y] == NonZero ==> update_env[y] != 0)
                    {
                        if y == x {
                            assert y in update_env;

                            assert update_env[x] == v;

                            assert stOut[x] == AbsEval(e, st);

                            if stOut[x] == Zero {
                                assert AbsEval(e, st) == Zero;
                                AbsZeroOkValueZero(e, st, env, v);
                                assert update_env[x] == 0;
                            }

                            if stOut[x] == NonZero {
                                assert AbsEval(e, st) == NonZero;
                                AbsNonZeroOkValueNonZero(e, st, env, v);
                                assert update_env[x] != 0;
                            }
                        } else {
                            assert stOut[y] == st[y];
                            assert y in st && y in env && y in update_env;

                            assert update_env[y] == env[y];

                            if stOut[y] == Zero {
                                assert st[y] == Zero;
                                assert env[y] == 0;
                                assert update_env[y] == 0;
                            }

                            if stOut[y] == NonZero {
                                assert st[y] == NonZero;
                                assert env[y] != 0;
                                assert update_env[y] != 0;
                            }
                        }
                    }
                }
            }
            case Err(_) => assert false;
        }

        case Seq(s1, s2) => {
            var r1 := AnalyzeStmt(s1, st);
            AnalyzeTrueExecValid(s1, st, env);

            match ExecStmt(s1, env)
            case Ok(env1) => {
                // From recursive ensures:
                assert Consistent(r1.1, env1);

                AnalyzeTrueExecValid(s2, r1.1, env1);

                // ExecStmt(Seq) definition:
                assert !IsErr(ExecStmt(Seq(s1, s2), env));
                // And output consistency comes from second recursive call
            }
            case Err(_) => assert false; // impossible by recursive soundness
        }

        case If(cond, t, f) => {
            assert CheckExpr(cond, st);
            CheckTrueEvalValid(cond, st, env);

            var absCond := AbsEval(cond, st);

            match EvalExpr(cond, env)
            case Ok(vc) => {
                match absCond
                case Zero => {
                    assert AnalyzeStmt(If(cond, t, f), st).1 == AnalyzeStmt(f, st).1;

                    AbsZeroOkValueZero(cond, st, env, vc);
                    assert vc == 0;

                    assert AnalyzeStmt(f, st).0;
                    AnalyzeTrueExecValid(f, st, env);

                    assert ExecStmt(If(cond, t, f), env) == ExecStmt(f, env);
                    assert !IsErr(ExecStmt(f, env));

                    match ExecStmt(f, env)
                    case Ok(envOut) => {
                        assert Consistent(AnalyzeStmt(f, st).1, envOut);
                        assert Consistent(AnalyzeStmt(If(cond, t, f), st).1, envOut);
                    }
                    case Err(_) => assert false;
                }
                case NonZero => {
                    assert AnalyzeStmt(If(cond, t, f), st).1 == AnalyzeStmt(t, st).1;

                    AbsNonZeroOkValueNonZero(cond, st, env, vc);
                    assert vc != 0;

                    assert AnalyzeStmt(t, st).0;
                    AnalyzeTrueExecValid(t, st, env);

                    assert ExecStmt(If(cond, t, f), env) == ExecStmt(t, env);
                    assert !IsErr(ExecStmt(t, env));

                    match ExecStmt(t, env)
                    case Ok(envOut) => {
                        assert Consistent(AnalyzeStmt(t, st).1, envOut);
                        assert Consistent(AnalyzeStmt(If(cond, t, f), st).1, envOut);
                    }
                    case Err(_) => assert false;
                }
                case Unknown => {
                    assert AnalyzeStmt(t, st).0;
                    assert AnalyzeStmt(f, st).0;

                    AnalyzeTrueExecValid(t, st, env);
                    AnalyzeTrueExecValid(f, st, env);

                    assert AnalyzeStmt(If(cond, t, f), st).1 == JoinState(AnalyzeStmt(t, st).1, AnalyzeStmt(f, st).1);

                    if vc == 0 {
                        assert ExecStmt(If(cond, t, f), env) == ExecStmt(f, env);

                        match ExecStmt(f, env)
                        case Ok(envOut) => {
                            assert Consistent(AnalyzeStmt(f, st).1, envOut);
                            ConsistentJoinRight(AnalyzeStmt(t, st).1, AnalyzeStmt(f, st).1, envOut);
                            assert Consistent(AnalyzeStmt(If(cond, t, f), st).1, envOut);
                        }
                        case Err(_) => assert false;
                    } else {
                        assert ExecStmt(If(cond, t, f), env) == ExecStmt(t, env);

                        match ExecStmt(t, env)
                        case Ok(envOut) => {
                            assert Consistent(AnalyzeStmt(t, st).1, envOut);
                            ConsistentJoinLeft(AnalyzeStmt(t, st).1, AnalyzeStmt(f, st).1, envOut);
                            assert Consistent(AnalyzeStmt(If(cond, t, f), st).1, envOut);
                        }
                        case Err(_) => assert false;
                    }
                }

                assert !IsErr(ExecStmt(If(cond,t,f), env));
            }
            case Err(_) => assert false; // cannot happen since CheckTrueEvalValid
        }
    }

    function AbsInit(env: Env): AbsState
    {
        map x | x in env ::
            if env[x] == 0 then Zero else NonZero
    }

    lemma AnalyzeProgramInput(p: Stmt, env: Env)
        requires AnalyzeStmt(p, AbsInit(env)).0
        ensures !IsErr(ExecStmt(p, env))
    {
        AnalyzeTrueExecValid(p, AbsInit(env), env);
    }

    lemma AnalyzeProgramSound(p: Stmt)
        requires AnalyzeProg(p)
        ensures !IsErr(ExecStmt(p, map[]))
    {
        AnalyzeTrueExecValid(p, map[], map[]);
    }

    function AnalyzeProg(p: Stmt): bool
    {
        AnalyzeStmt(p, map[]).0
    }
}
