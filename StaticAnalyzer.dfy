// ECS 261 Final Project
// StaticAnalyzer.dfy

include "Types.dfy" 

module StaticAnalyzer {    
    import opened Types

    // Expression evaluation (runtime simulation)
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

        // If e is a modulo between two expressions, evaluate the expressions, checking for errors.
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

    // Abstract evaluation of an expression
    function AbsEval(e: Expr, state: AbsState): AbsVal        
        decreases e
    {
        match e
        // if constant, simply evaluate the constant.
        case Const(n) => if n == 0 then Zero else if n > 0 then Positive else Negative

        // if variable, check if the variable exists, and use that state.
        case Var(x) => if x in state then state[x] else Unknown

        // for addition check all the valid cases where we can evaluate the abstract value, else unknown
        case Add(a,b) =>
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);
            
            if a_eval == Zero && b_eval == Zero then Zero
            else if a_eval == Positive && b_eval == Zero then Positive
            else if a_eval == Negative && b_eval == Zero then Negative
            else if a_eval == Zero && b_eval == Positive then Positive
            else if a_eval == Zero && b_eval == Negative then Negative
            else if a_eval == Positive && b_eval == Positive then Positive
            else if a_eval == Negative && b_eval == Negative then Negative
            else Unknown

        // for subtraction check all the valid cases where we can evaluate the abstract value, else unknown
        case Sub(a,b) =>
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);
            
            if a_eval == Zero && b_eval == Zero then Zero
            else if a_eval == Positive && b_eval == Zero then Positive
            else if a_eval == Negative && b_eval == Zero then Negative
            else if a_eval == Zero && b_eval == Positive then Negative
            else if a_eval == Zero && b_eval == Negative then Positive
            else if a_eval == Positive && b_eval == Negative then Positive
            else if a_eval == Negative && b_eval == Positive then Negative
            else Unknown

        // for mult check all the valid cases where we can evaluate the abstract value, else unknown
        case Mul(a,b) =>
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);

            if a_eval == Zero || b_eval == Zero then Zero
            else if a_eval == Positive && b_eval == Positive then Positive
            else if a_eval == Negative && b_eval == Negative then Positive
            else if a_eval == Positive && b_eval == Negative then Negative
            else if a_eval == Negative && b_eval == Positive then Negative
            else Unknown

        // for div check all the valid cases where we can evaluate the abstract value, else unknown
        case Div(a, b) => 
            var a_eval := AbsEval(a, state);
            var b_eval := AbsEval(b, state);
            if a_eval == Zero then Zero
            else Unknown
        
        // for mult check all the valid cases where we can evaluate the abstract value, else unknown
        case Mod(a, b) => 
            var a_eval := AbsEval(a, state);            
            if a_eval == Zero then Zero
            else Unknown
    }
    
    function CheckExpr(e: Expr, state: AbsState): bool
        decreases e
    {
        match e

        // if constant, then automatically valid
        case Const(n) => true

        // if variable, then check if variable name is in state.
        case Var(x) => x in state

        // if add operation, recursively check both subexp.
        case Add(a,b) => CheckExpr(a, state) && CheckExpr(b, state)
        
        // if sub operation, recursively check both subexp.
        case Sub(a,b) => CheckExpr(a, state) && CheckExpr(b, state)
        
        // if mul operation, recursively check both subexp.
        case Mul(a,b) => CheckExpr(a, state) && CheckExpr(b, state)

        // if div operation, recursively check both subexp. additionally check abseval on denom for zero/unknown.
        case Div(a,b) => CheckExpr(a, state) && CheckExpr(b, state) && (AbsEval(b, state) == Positive || AbsEval(b, state) == Negative)

        // if mod operation, recursively check both subexp. additionally check abseval on denom for zero/unknown.
        case Mod(a,b) => CheckExpr(a, state) && CheckExpr(b, state) && (AbsEval(b, state) == Positive || AbsEval(b, state) == Negative)
    }

    // helper for joinstate, combine two absval (if they are unequal, result in unknown)
    function JoinVal(a: AbsVal, b: AbsVal): AbsVal
    {
        if a == b then a else Unknown
    }

    // joins two states (used in analysis of if statements)
    function JoinState(s1: AbsState, s2: AbsState): AbsState
    {
        map k | k in s1 && k in s2 :: JoinVal(s1[k], s2[k])
    }

    // main function for static analyzer.
    function AnalyzeStmt(s: Stmt, state: AbsState): (bool, AbsState)
        decreases s
    {
        match s

        // skip statement will trivially be safe
        case Skip => (true, state)

        // verify the expression e is valid, if so, then safe otherwise not.
        case Assign(x, e) =>
            if CheckExpr(e, state)
            then (true, state[x := AbsEval(e, state)])
            else (false, state)
        
        // recursively analyze both sub statements.
        case Seq(s1, s2) =>
            match AnalyzeStmt(s1, state){
                case (false, state_f_s1) => (false, state_f_s1)
                case (true, state_t_s1) => AnalyzeStmt(s2, state_t_s1)
            }

        // if condition
        case If(cond, then_statement, else_statement) =>
            // first check the condition expression.
            if(CheckExpr(cond, state))
                then match AbsEval(cond, state)
                    // if positive or negative analyze then statement only (pruning)
                    case Positive => AnalyzeStmt(then_statement, state)
                    case Negative => AnalyzeStmt(then_statement, state)
                    // if zero analyze else statement only (pruning)
                    case Zero => AnalyzeStmt(else_statement, state)
                    // if unknown analyze both statements.
                    case Unknown => match AnalyzeStmt(then_statement, state){
                            case (false, state_f_then) => (false, state_f_then)
                            case (true, state_t_then) =>
                                match AnalyzeStmt(else_statement, state) {
                                    case (false, state_f_else) => (false, state_f_else)
                                    // use join statement to take the intersection of both sides.
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

    // important invariant: verifies consistency between abstract state and env (used as precondition)
    predicate Consistent(st: AbsState, env: Env){
        forall x :: x in st ==>
            x in env &&
            (st[x] == Zero ==> env[x] == 0) &&
            (st[x] == Positive ==> env[x] > 0) &&
            (st[x] == Negative ==> env[x] < 0)
    }

    // lemma: if absstate indicates positive, then the env will have a positive value for the variable at that state.
    lemma {:vcs_split_on_every_assert} AbsPositiveOkValuePositive(e: Expr, st: AbsState, env: Env, v: int)
        requires AbsEval(e, st) == Positive
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        requires EvalExpr(e, env) == Ok(v)
        ensures v > 0
        decreases e
    {
        match e
        
        // if constant, simply check the value if positive.
        case Const(n) => {
            assert n > 0;
            assert v == n;
        }

        // if variable, the variable must exist and value must match as well.
        case Var(x) => {
            assert x in st && x in env;
            assert st[x] == Positive;
            assert env[x] > 0;
            assert v == env[x];
        }

        // if add then verify expression evaluates to positive
        case Add(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Zero) || (va == Zero && vb == Positive) || (va == Positive && vb == Positive);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 + v2;
                    // assert each of the cases, positive can be possible.
                    if va == Zero {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 == 0;
                        assert v2 > 0;
                    } else if vb == Zero {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v1 > 0;
                        assert v2 == 0;
                    } else {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 > 0 && v2 > 0;
                    }
                    assert v > 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // sub case, similar to add case
        case Sub(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Zero) || (va == Zero && vb == Negative) || (va == Positive && vb == Negative);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 - v2;
                    if va == Positive && vb == Zero {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v1 > 0 && v2 == 0;
                    } else if va == Zero && vb == Negative {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 == 0 && v2 < 0;
                    } else {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 > 0 && v2 < 0;
                    }
                    assert v > 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // mul case, similar to add case
        case Mul(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Positive) || (va == Negative && vb == Negative);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 * v2;
                    if va == Positive {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 > 0 && v2 > 0;
                    } else {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 < 0 && v2 < 0;
                    }
                    assert v > 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // div case, since you can never fully assert a positive (non-zero) result from module, given my language syntax, it's impossible.
        case Div(a,b) => assert false;

        // mod case, since you can never fully assert a positive (non-zero) result from module, given my language syntax, it's impossible.
        case Mod(a,b) => assert false;
    }

    // lemma: if absstate indicates negative, then the env will have a negative value for the variable at that state.
    lemma {:vcs_split_on_every_assert} AbsNegativeOkValueNegative(e: Expr, st: AbsState, env: Env, v: int)
        requires AbsEval(e, st) == Negative
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        requires EvalExpr(e, env) == Ok(v)
        ensures v < 0
        decreases e
    {
        match e
        // constant case, verify that constant is negative
        case Const(n) => {
            assert n < 0;
            assert v == n;
        }

        // variable case, assert the variable exists in both state and env and that the val is negative 
        case Var(x) => {
            assert x in st && x in env;
            assert st[x] == Negative;
            assert env[x] < 0;
            assert v == env[x];
        }

        // add case 
        case Add(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Negative && vb == Zero) || (va == Zero && vb == Negative) || (va == Negative && vb == Negative);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            // assert each of the cases, negative can be possible.
            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 + v2;
                    if va == Zero {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 == 0;
                        assert v2 < 0;
                    } else if vb == Zero {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v1 < 0;
                        assert v2 == 0;
                    } else {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 < 0 && v2 < 0;
                    }
                    assert v < 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // sub case
        case Sub(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Negative && vb == Zero) || (va == Zero && vb == Positive) || (va == Negative && vb == Positive);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 - v2;
                    if va == Negative && vb == Zero {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v1 < 0 && v2 == 0;
                    } else if va == Zero && vb == Positive {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 == 0 && v2 > 0;
                    } else {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 < 0 && v2 > 0;
                    }
                    assert v < 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // mul case
        case Mul(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Negative) || (va == Negative && vb == Positive);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 * v2;
                    if va == Positive {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 > 0 && v2 < 0;
                    } else {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 < 0 && v2 > 0;
                    }
                    assert v < 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // div case
        case Div(a,b) => assert false;

        // mod never results in negative
        case Mod(a,b) => assert false;
    }

    lemma {:vcs_split_on_every_assert} AbsNonZeroOkValueNonZero(e: Expr, st: AbsState, env: Env, v: int)
        requires (AbsEval(e, st) == Positive || AbsEval(e, st) == Negative) 
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        requires EvalExpr(e, env) == Ok(v)
        ensures v != 0
        decreases e
    {
        match e

        // constant case: assert that the value is NonZero
        case Const(n) => {
            assert n != 0;
            assert v == n;
        }

        // variable case: assert that the value exists and it's NonZero
        case Var(x) => {
            assert x in st && x in env;
            if st[x] == Positive {
                assert env[x] > 0;
            } else {
                assert st[x] == Negative;
                assert env[x] < 0;
            }
            assert v == env[x];
        }

        // add case, cover all potential add combinations as defined in AbsEval
        case Add(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Zero) || (va == Zero && vb == Positive) ||
                   (va == Negative && vb == Zero) || (va == Zero && vb == Negative) ||
                   (va == Positive && vb == Positive) || (va == Negative && vb == Negative);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 + v2;
                    if va == Zero {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsNonZeroOkValueNonZero(b, st, env, v2);
                        assert v1 == 0;
                    } else if vb == Zero {
                        AbsNonZeroOkValueNonZero(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v2 == 0;
                    } else if va == Positive {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v1 > 0 && v2 > 0;
                    } else {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v1 < 0 && v2 < 0;
                    }
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // sub case, same as add more or less
        case Sub(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Zero) || (va == Zero && vb == Negative) || (va == Positive && vb == Negative) ||
                   (va == Negative && vb == Zero) || (va == Zero && vb == Positive) || (va == Negative && vb == Positive);

            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    assert v == v1 - v2;
                    if va == Positive && vb == Zero {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v1 > 0;
                    } else if va == Zero && vb == Negative {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                        assert v2 < 0;
                    } else if va == Positive && vb == Negative {
                        AbsPositiveOkValuePositive(a, st, env, v1);
                        AbsNegativeOkValueNegative(b, st, env, v2);
                    } else if va == Negative && vb == Zero {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsZeroOkValueZero(b, st, env, v2);
                        assert v1 < 0;
                    } else if va == Zero && vb == Positive {
                        AbsZeroOkValueZero(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                        assert v2 > 0;
                    } else {
                        AbsNegativeOkValueNegative(a, st, env, v1);
                        AbsPositiveOkValuePositive(b, st, env, v2);
                    }
                    assert v != 0;
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // mul case, same as add more or less
        case Mul(a,b) => {
            var va := AbsEval(a, st);
            var vb := AbsEval(b, st);
            assert (va == Positive && vb == Positive) || (va == Negative && vb == Negative) ||
                   (va == Positive && vb == Negative) || (va == Negative && vb == Positive);

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

        //div case, mod cannot be asserted to be nonzero in any case.
        case Div(a,b) => assert false;

        //mod case, mod cannot be asserted to be nonzero in any case.
        case Mod(a,b) => assert false;
    }

    // If AbsEval says "Zero", then any Ok(v) must be v == 0
    lemma {:vcs_split_on_every_assert} AbsZeroOkValueZero(e: Expr, st: AbsState, env: Env, v: int)
        requires AbsEval(e, st) == Zero
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        requires EvalExpr(e, env) == Ok(v)
        ensures v == 0
        decreases e
    {
        match e
        // assert if exp is a const and abseval gives 0, then the constant value is 0.
        case Const(n) => {
            assert n == 0;
            assert v == 0;
        }

        // var case: assert that the item exists in state and env, and that it equals 0.
        case Var(x) => {
            assert x in st;
            assert x in env;
            assert st[x] == Zero;
            assert env[x] == 0;
            assert v == env[x];
        }

        // add case: go through each possibility for add, and assert every case to be working towards resulting in 0.
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

        // sub case: same as add more or less
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

        // mul case: same as add more or less
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

        // div case: same as add more or less
        case Div(a,b) => {
            assert AbsEval(a, st) == Zero && (AbsEval(b, st) == Positive || AbsEval(b, st) == Negative);
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

        // mod case: same as add more or less
        case Mod(a,b) => {
            assert AbsEval(a, st) == Zero && (AbsEval(b, st) == Positive || AbsEval(b, st) == Negative);

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

    // this lemma asserts that if checkexpr indicates a given expression is safe
    // then that expression will not result in an error when evaluated.
    lemma CheckTrueEvalValid(e: Expr, st: AbsState, env: Env)
        requires CheckExpr(e, st)
        requires Consistent(st, env)
        ensures !IsErr(EvalExpr(e, env))
        decreases e
    {
        match e
        // trivial: if we have a constant, we simply can assert that the result is as expected.
        case Const(n) => {
            assert EvalExpr(Const(n), env) == Ok(n);
        }

        // we can assert that x exists in both st and env due to check expr and consistency precond's
        case Var(x) => {
            assert x in st;
            assert x in env;
            // we can assert that the values will be same as well on evaluation
            assert EvalExpr(Var(x), env) == Ok(env[x]);
        }

        // add case
        case Add(a,b) => {
            //assert that both subexpressions are safe, and eval are valid (recursive calls)
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            // assert that the expected results result in the sum of the two values.
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

        // sub case
        case Sub(a,b) => {
            //assert that both subexpressions are safe, and eval are valid (recursive calls)
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            // assert that the expected results result in the difference of the two values.
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

        // mul case
        case Mul(a,b) => {
            //assert that both subexpressions are safe, and eval are valid (recursive calls)
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);

            // assert that the expected results result in the product of the two values.
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

        // div case
        case Div(a,b) => {
            //assert that both subexpressions are safe, and eval are valid (recursive calls)
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);
            // additional assert for denom
            assert AbsEval(b, st) == Positive || AbsEval(b, st) == Negative;

            // assert that the expected results result in the quotient of the two values.
            match EvalExpr(a, env)
            case Ok(v1) => {
                match EvalExpr(b, env)
                case Ok(v2) => {
                    // use helper lemma (if abstate indicates nonzero denom (i.e. pos || neg), then the value in env is nonzero as well.)
                    AbsNonZeroOkValueNonZero(b, st, env, v2);
                    assert v2 != 0;
                    assert EvalExpr(Div(a,b), env) == Ok(v1 / v2);
                }
                case Err(_) => assert false;
            }
            case Err(_) => assert false;
        }

        // mod case, similar in structure to div case.
        case Mod(a,b) => {
            assert CheckExpr(a, st) && CheckExpr(b, st);
            CheckTrueEvalValid(a, st, env);
            CheckTrueEvalValid(b, st, env);
            assert AbsEval(b, st) == Positive || AbsEval(b, st) == Negative;

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

    // this lemma is used for the case when an if cond evaluates to Unknown, and we need to maintain the consistency inv
    // if the runtime env travels down the then path, its absstate will match the join path's absstate.
    lemma ConsistentJoinLeft(stT: AbsState, stF: AbsState, env: Env)
        requires Consistent(stT, env)
        ensures Consistent(JoinState(stT, stF), env)
    {
        forall k | k in JoinState(stT, stF)
            ensures k in env
            ensures (JoinState(stT, stF)[k] == Zero ==> env[k] == 0)
            ensures (JoinState(stT, stF)[k] == Positive ==> env[k] > 0)
            ensures (JoinState(stT, stF)[k] == Negative ==> env[k] < 0)
        {
            assert k in stT && k in stF;
            assert k in env;

            if JoinState(stT, stF)[k] == Zero {
                assert stT[k] == Zero;
                assert env[k] == 0;
            }
            if JoinState(stT, stF)[k] == Positive {
                assert stT[k] == Positive;
                assert env[k] > 0;
            }
            if JoinState(stT, stF)[k] == Negative {
                assert stT[k] == Negative;
                assert env[k] < 0;
            }
        }
    }

    // this lemma is used for the case when an if cond evaluates to Unknown, and we need to maintain the consistency inv
    // if the runtime env travels down the else path, its absstate will match the join path's absstate.
    lemma ConsistentJoinRight(stT: AbsState, stF: AbsState, env: Env)
        requires Consistent(stF, env)
        ensures Consistent(JoinState(stT, stF), env)
    {
        forall k | k in JoinState(stT, stF)
            ensures k in env
            ensures (JoinState(stT, stF)[k] == Zero ==> env[k] == 0)
            ensures (JoinState(stT, stF)[k] == Positive ==> env[k] > 0)
            ensures (JoinState(stT, stF)[k] == Negative ==> env[k] < 0)
        {
            assert k in stT && k in stF;
            assert k in env;

            if JoinState(stT, stF)[k] == Zero {
                assert stF[k] == Zero;
                assert env[k] == 0;
            }
            if JoinState(stT, stF)[k] == Positive {
                assert stF[k] == Positive;
                assert env[k] > 0;
            }
            if JoinState(stT, stF)[k] == Negative {
                assert stF[k] == Negative;
                assert env[k] < 0;
            }
        }
    }
    
    // key lemma: essentially if analyzestmt returns true, then execstmt will not result in an error (soundness)
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

        // skip case: trivial simply assert no issue will happen.
        case Skip() => assert ExecStmt(Skip(), env) == Ok(env);

        // assign case: 
        case Assign(x, e) => {
            // check the the expression itself.
            assert CheckExpr(e, st);
            CheckTrueEvalValid(e, st, env);

            match EvalExpr(e, env)
            case Ok(v) => {
                // update the environment (simulating the behavior of Assign itself)
                var update_env := Update(env, x, v);
                // prove the soundness implication 
                assert ExecStmt(Assign(x, e), env) == Ok(update_env);
                var stOut := AnalyzeStmt(Assign(x, e), st).1;
                assert stOut == st[x := AbsEval(e, st)];
                
                // assert the consistency postcondition.
                assert Consistent(stOut, update_env) by 
                {
                    // loop through each item in output state and check if it's consistent.
                    forall y | y in stOut
                        ensures y in update_env
                        ensures (stOut[y] == Zero ==> update_env[y] == 0)
                        ensures (stOut[y] == Positive ==> update_env[y] > 0)
                        ensures (stOut[y] == Negative ==> update_env[y] < 0)
                    {
                        if y == x {
                            // assert that the new element has correctly been added
                            assert y in update_env;

                            assert update_env[x] == v;

                            assert stOut[x] == AbsEval(e, st);

                            if stOut[x] == Zero {
                                assert AbsEval(e, st) == Zero;
                                AbsZeroOkValueZero(e, st, env, v);
                                assert update_env[x] == 0;
                            }

                            if stOut[x] == Positive {
                                assert AbsEval(e, st) == Positive;
                                AbsPositiveOkValuePositive(e, st, env, v);
                                assert update_env[x] > 0;
                            }

                            if stOut[x] == Negative {
                                assert AbsEval(e, st) == Negative;
                                AbsNegativeOkValueNegative(e, st, env, v);
                                assert update_env[x] < 0;
                            }
                        } else {
                            // assert all old elements are here.
                            assert stOut[y] == st[y];
                            assert y in st && y in env && y in update_env;

                            assert update_env[y] == env[y];

                            if stOut[y] == Zero {
                                assert st[y] == Zero;
                                assert env[y] == 0;
                                assert update_env[y] == 0;
                            }

                            if stOut[y] == Positive {
                                assert st[y] == Positive;
                                assert env[y] != 0;
                                assert update_env[y] > 0;
                            }

                            if stOut[y] == Negative {
                                assert st[y] == Negative;
                                assert env[y] != 0;
                                assert update_env[y] < 0;
                            }
                        }
                    }
                }
            }
            case Err(_) => assert false;
        }

        // sequence case: (tricky to maintain consistency btwn two statements (done with invariant))
        case Seq(s1, s2) => {
            var r1 := AnalyzeStmt(s1, st);
            // show that s1 on it's own is correct w/ recurisve call
            AnalyzeTrueExecValid(s1, st, env);
            
            match ExecStmt(s1, env)
            case Ok(env1) => {
                // show the abs state from analyzing s1 and the env from execution is consistent
                assert Consistent(r1.1, env1);
                // show that s2 on it's own is correct w/ recurisve call
                AnalyzeTrueExecValid(s2, r1.1, env1);
                // we can assert no error from this case.
                assert !IsErr(ExecStmt(Seq(s1, s2), env));
            }
            case Err(_) => assert false;
        }

        // if case: 
        case If(cond, t, f) => {
            // assert that the cond expression is valid and then evaluate it (using abseval)
            assert CheckExpr(cond, st);
            CheckTrueEvalValid(cond, st, env);
            var absCond := AbsEval(cond, st);

            // ensure that the abseval dictates the correct direction and that all three potential paths are validated and consistent.
            match EvalExpr(cond, env)
            case Ok(vc) => {
                match absCond
                // if zero, only need to look down else path
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
                // if positive/negative, only need to look down else path (wrote twice for thoroughness, though code in each case is identical)
                case Positive => {
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
                case Negative => {
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
                // if unknown, we need to use join state to take the intersection.
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

    // initialize abs state if given a non-empty env to start.
    function AbsInit(env: Env): AbsState
    {
        map x | x in env :: Unknown // if env[x] == 0 then Zero else if env[x] > 0 then Positive else Negative
    }

    // wrapper function for analyze statement to extract the result (safe/unsafe).
    function AnalyzeProgram(p: Stmt, env: Env): bool
    {
        AnalyzeStmt(p, AbsInit(env)).0
    }

    // main soundness lemma: If AnalyzeProgram indicates safe for a program (precond)
    // then we will not have an error when executing the program. (postcond)
    lemma AnalyzeProgramSound(p: Stmt, env: Env)
        ensures AnalyzeProgram(p, env) ==> !IsErr(ExecStmt(p, env))
    {
        if AnalyzeProgram(p, env){ 
            AnalyzeTrueExecValid(p, AbsInit(env), env);
        }
    }
}
