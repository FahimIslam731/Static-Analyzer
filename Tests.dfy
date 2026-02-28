include "StaticAnalyzer.dfy" 

module Tests{
    import opened StaticAnalyzer

    method TestCase1(){
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Div(Var("v"), Const(2)));
        var stmt3 := Seq(stmt1, stmt2);
        var env := map[];
        
        AnalyzeProgramSound(stmt3, env);
        assert AnalyzeStmt(stmt3, {}).0;
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 4;
        case Err(e1) => assert false;
    }

    method TestCase2(){
        var stmt := Assign("y", Add(Var("x"), Const(1)));
        assert !AnalyzeStmt(stmt, {}).0;
        var env := map[];
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == UninitializedVar("x");
    }

    method TestCase3(){
        var cond_expr := Const(1);
        var stmt_then := Assign("x", Const(1));
        var stmt_else := Assign("x", Const(0));
        var stmt := If(cond_expr, stmt_then, stmt_else);
        var env := map[];

        AnalyzeProgramSound(stmt, env);

        assert AnalyzeStmt(stmt, {}).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1;
        case Err(e1) => assert false;
    }

    method TestCase4(){
        var cond_expr := Const(1);
        var stmt_then := Assign("x", Const(1));
        var stmt_else := Assign("y", Const(0));
        var if_stmt := If(cond_expr, stmt_then, stmt_else);
        var stmt := Seq(if_stmt, Assign("z", Var("x")));
        var env := map[];

        assert !AnalyzeStmt(stmt, {}).0;    
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1;
        case Err(e1) => assert false;
    }

    method TestCase5(){
        var stmt := Assign("z", Div(Const(1), Const(0)));
        var env := map[];

        assert !AnalyzeStmt(stmt, {}).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == DivByZero();
    }

    method TestCase6(){
        var stmt := Assign("z", Div(Const(12), Add(Const(2), Const(2))));
        var env := map[];

        assert !AnalyzeStmt(stmt, {}).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["z"] == 3;
        case Err(e1) => assert false;
    }

    method TestCase7(){
        var cond := Add(Const(1), Const(-1));
        var stmt1 := Assign("v", Mul(Const(4), Const(4)));
        var stmt2 := Assign("v", Sub(Var("v"), Const(2)));
        var stmt3 := If(cond, Assign("v", Const(30)), Seq(stmt1, stmt2));
        
        assert AnalyzeStmt(stmt3, {}).0;
        var env := map[];
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 14;
        case Err(e1) => assert false;
    }
}