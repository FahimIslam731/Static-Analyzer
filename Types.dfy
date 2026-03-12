// ECS 261 Final Project
// Types.dfy

module Types{
    // AST Syntax Definition

    // abstract state of variables, not like the dynamically updated map of variables but is able to track certain aspects of the variables
    datatype AbsVal = Zero | Positive | Negative | Unknown
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
    // If a variable is missing from the map, it is "uninitialized", and it will cause an error if it is accessed (without having been initialized).
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
}