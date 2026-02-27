// ECS 261 Project
// StaticAnalyzer.dfy

module StaticAnalyzer {
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

    function CheckExpr(s: Stmt, env: Env): Result<Env>
    {
        //placeholder
        Err(DivByZero)
    }

}