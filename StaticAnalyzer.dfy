// ECS 261 Final Project
// StaticAnalyzer.dfy

module StaticAnalyzer {
    // abstract state of variables, not like the dynamically updated map of variables
    type Defs = set<string>
    
    // AST Syntax Definition

    // Expression datatype
    datatype Expr =
        | Const(n: int)
        | Var(x: string)
        | Add(e1: Expr, e2: Expr)
        | Sub(e1: Expr, e2: Expr)
        | Mul(e1: Expr, e2: Expr)
        | Div(e1: Expr, e2: Expr)
        // | Mod(e1: Expr, e2: Expr) // Potentially add this

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
        // Cool note about this, since a new map is made every time an entry is added,
        // You can't just have a postcondition like 'ensures x in env'
        ensures x in Update(env, x, v)
        ensures Update(env, x, v)[x] == v
    {
        env[x := v]
    }

    // -----------------------------
    // 3) Expression evaluation (runtime)
    // -----------------------------
    function EvalExpr(e: Expr, env: Env): Result<int>
        //requires CheckExpr(e, env.Keys)
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

        // If e is a multiplication between two expressions, evaluate the expressions and add them addition, checking for errors.
        case Mul(a,b) =>
            match EvalExpr(a, env) {
            case Err(er) => Err(er)
            case Ok(v1) =>
                match EvalExpr(b, env) {
                case Err(er) => Err(er)
                case Ok(v2) => Ok(v1 * v2)
                }
            }

        // If e is a division between two expressions, evaluate the addition, checking for errors.
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

    function CheckExpr(e: Expr, defs: Defs): bool
        decreases e
    {
        match e

        case Const(n) => true

        case Var(x) => x in defs

        case Add(a,b) => CheckExpr(a, defs) && CheckExpr(b, defs)
        
        case Sub(a,b) => CheckExpr(a, defs) && CheckExpr(b, defs)
        
        case Mul(a,b) => CheckExpr(a, defs) && CheckExpr(b, defs)

        case Div(a,b) => CheckExpr(a, defs) && CheckExpr(b, defs) && match b {
                case Const(n) => n != 0
                case _ => false
            }
        // to be clear this is sound but not complete.
        // it's possible for there to be a valid example where we have a
        // variable or a subexpression which evaluates to 0, but for the 
        // sake of simplicity early on this will only allow validity if denom is a non-zero constant.
    }

    function AnalyzeStmt(s: Stmt, defs: Defs): (bool, Defs)
        decreases s
    {
        match s

        case Skip => (true, defs)

        case Assign(x, e) =>
            match CheckExpr(e, defs){
                case false => (false, defs)
                case true  => (true, defs + {x})
            }

        case Seq(s1, s2) =>
            match AnalyzeStmt(s1, defs){
                case (false, defs_f_s1) => (false, defs_f_s1)
                case (true, defs_t_s1) =>
                    match AnalyzeStmt(s2, defs_t_s1){
                    case (false, defs_f_s2) => (false, defs_f_s2)
                    case (true, defs_t_s2) => (true, defs_t_s2)
                }
            } 

        case If(cond, then_statement, else_statement) =>
            match CheckExpr(cond, defs){
                case false => (false, defs)
                case true =>
                match AnalyzeStmt(then_statement, defs){
                    case (false, defs_f_then) => (false, defs_f_then)
                    case (true, defs_t_then) =>
                        match AnalyzeStmt(else_statement, defs) {
                            case (false, defs_f_else) => (false, defs_f_else)
                            case (true, defs_t_else) => (true, defs_t_then * defs_t_else)
                        }
                }
            }
    }

    // helper predicate for an error function
    predicate IsErr(r: Result){
        match r
        case Ok(_) => false
        case Err(_) => true
    }

    // key lemma: if CheckExpr returns true (meaning expression is safe), then EvalExpr will not result in an error.
    lemma CheckTrueEvalValid(e: Expr, defs: Defs, env: Env)
        requires CheckExpr(e, defs)
        requires forall v :: v in defs ==> v in env
        ensures !IsErr(EvalExpr(e, env))
        decreases e
    {        
        match e

        case Const(x) => {
            assert EvalExpr(Const(x), env) == Ok(x);
            assert !IsErr(Ok(x));
            assert !IsErr(EvalExpr(e, env));
        }

        case Var(x) => {
            assert x in env && x in defs;
            assert EvalExpr(Var(x), env) == Ok(env[x]);
            assert !IsErr(Ok(env[x]));
            assert !IsErr(EvalExpr(e, env));
        }

        case Add(x1, x2) => {
            assert CheckExpr(x1, defs) && CheckExpr(x2, defs);
            
            CheckTrueEvalValid(x1, defs, env);
            CheckTrueEvalValid(x2, defs, env);

            match EvalExpr(x1, env)
            case Ok(v1) => {
                match EvalExpr(x2, env)
                case Ok(v2) => {
                    assert EvalExpr(Add(x1, x2), env) == Ok(v1 + v2);
                    assert !IsErr(Ok(v1 + v2));
                    assert !IsErr(EvalExpr(e, env));
                }
                case Err(e2) => assert false; // impossible, already know not erroneous
            }
            case Err(e1) => assert false; // impossible, already know not erroneous
        }

        case Sub(x1, x2) => {
            assert CheckExpr(x1, defs) && CheckExpr(x2, defs);
            
            CheckTrueEvalValid(x1, defs, env);
            CheckTrueEvalValid(x2, defs, env);

            match EvalExpr(x1, env)
            case Ok(v1) => {
                match EvalExpr(x2, env)
                case Ok(v2) => {
                    assert EvalExpr(Sub(x1, x2), env) == Ok(v1 - v2);
                    assert !IsErr(Ok(v1 - v2));
                    assert !IsErr(EvalExpr(e, env));
                }
                case Err(e2) => assert false; // impossible, already know not erroneous
            }
            case Err(e1) => assert false; // impossible, already know not erroneous
        }

        case Mul(x1, x2) => {
            assert CheckExpr(x1, defs) && CheckExpr(x2, defs);
            
            CheckTrueEvalValid(x1, defs, env);
            CheckTrueEvalValid(x2, defs, env);

            match EvalExpr(x1, env)
            case Ok(v1) => {
                match EvalExpr(x2, env)
                case Ok(v2) => {
                    assert EvalExpr(Mul(x1, x2), env) == Ok(v1 * v2);
                    assert !IsErr(Ok(v1 * v2));
                    assert !IsErr(EvalExpr(e, env));
                }
                case Err(e2) => assert false; // impossible, already know not erroneous
            }
            case Err(e1) => assert false; // impossible, already know not erroneous
        }

        case Div(x1, x2) => {
            assert CheckExpr(x1, defs) && CheckExpr(x2, defs);
            
            CheckTrueEvalValid(x1, defs, env);
            CheckTrueEvalValid(x2, defs, env);

            match x2
            case Const(n) => {
                assert n != 0;
                match EvalExpr(x2, env)
                    case Ok(v2) => {
                        assert v2 != 0;
                        match EvalExpr(x1, env)
                        case Ok(v1) => {
                            assert EvalExpr(Div(x1, x2), env) == Ok(v1 / v2);
                            assert !IsErr(Ok(v1 / v2));
                            assert !IsErr(EvalExpr(e, env));
                        }
                        case Err(e1) => assert false; // impossible, already know not erroneous
                    }
                    case Err(e2) => assert false; // impossible, already know not erroneous
            }
            case _ => assert false; // impossible, already know not erroneous
        }
    }
    
    // key lemma: if AnalyzeStmt returns true (meaning statement is safe), then ExecStmt will not result in an error.
    lemma AnalyzeTrueExecValid(s: Stmt, defs: Defs, env: Env)
        requires AnalyzeStmt(s, defs).0
        requires forall v :: v in defs ==> v in env
        ensures !IsErr(ExecStmt(s, env))
        ensures match ExecStmt(s, env)
          case Ok(envOut) =>
            forall v :: v in AnalyzeStmt(s, defs).1 ==> v in envOut
          case Err(_) => true
        decreases s
    {        
        match s

        case Skip() => {
            assert ExecStmt(Skip(), env) == Ok(env);
            assert !IsErr(Ok(env));
            assert !IsErr(ExecStmt(s, env));
            assert forall v :: v in AnalyzeStmt(Skip(), defs).1 ==> v in env;
        }

        case Assign(key, value) => {
            assert CheckExpr(value, defs);
            CheckTrueEvalValid(value, defs, env);
            
            match EvalExpr(value, env)
            case Ok(v) => {
                assert ExecStmt(Assign(key, value), env) == Ok(Update(env, key, v));
                assert forall x :: x in AnalyzeStmt(Assign(key, value), defs).1 ==> x in Update(env, key, v);
                assert !IsErr(Ok(Update(env, key, v)));
                assert !IsErr(ExecStmt(s, env));
            }
            case Err(e1) => assert false; // impossible, already know not erroneous
        }

        case Seq(s1, s2) => {
            var r1 := AnalyzeStmt(s1, defs);
            AnalyzeTrueExecValid(s1, defs, env);
            
            match ExecStmt(s1, env)
            case Ok(env1) => assert forall v :: v in r1.1 ==> v in env1;
            case Err(e1) => assert false;
            
            match ExecStmt(s1, env)
            case Ok(env1) => {
                AnalyzeTrueExecValid(s2, r1.1, env1);
                assert !IsErr(ExecStmt(Seq(s1, s2), env));
            }
            case Err(er) => assert false; // Impossible because we already proved s1 doesn't error
        }

        case If(cond, then_stmt, else_stmt) => {
            assert CheckExpr(cond, defs) && AnalyzeStmt(then_stmt, defs).0 && AnalyzeStmt(else_stmt, defs).0;
            CheckTrueEvalValid(cond, defs, env);

            AnalyzeTrueExecValid(then_stmt, defs, env);
            AnalyzeTrueExecValid(else_stmt, defs, env);
            
            match EvalExpr(cond, env)
            case Ok(v) => {
                if(v == 0){
                    assert ExecStmt(If(cond, then_stmt, else_stmt), env) == ExecStmt(else_stmt, env);
                    assert !IsErr(ExecStmt(else_stmt, env));
                } else{
                    assert ExecStmt(If(cond, then_stmt, else_stmt), env) == ExecStmt(then_stmt, env);
                    assert !IsErr(ExecStmt(then_stmt, env));
                }
                assert !IsErr(ExecStmt(If(cond, then_stmt, else_stmt), env));
            }
            case Err(e1) => assert false; // Impossible because we already asserted no error.
        }
    }

    lemma AnalyzeProgramSound(p: Stmt, env: Env)
        requires AnalyzeStmt(p, {}).0
        ensures !IsErr(ExecStmt(p, env))
    {
        AnalyzeTrueExecValid(p, {}, env);
    }
}
