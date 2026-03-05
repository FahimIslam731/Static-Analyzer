include "StaticAnalyzer.dfy" 

module Tests{
    import opened StaticAnalyzer

    method TestCase1(){
        /*
        v := 4 + 4;
        v := v / 2;
        */
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Div(Var("v"), Const(2)));
        var stmt3 := Seq(stmt1, stmt2);
        var env := map[];
        var state := map[];
        
        AnalyzeProgramSound(stmt3, env);
        assert AnalyzeStmt(stmt3, state).0;
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 4;
        case Err(e1) => assert false;
    }

    method TestCase2(){
        /*
        y := x + 1;
        */
        var stmt := Assign("y", Add(Var("x"), Const(1)));
        var state := map[];
        assert !AnalyzeStmt(stmt, state).0;
        var env := map[];
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == UninitializedVar("x");
    }

    method TestCase3(){
        /*
        if(1){
            x := 1;
        } else{
            x := 0;
        }
        */
        var cond_expr := Const(1);
        var stmt_then := Assign("x", Const(1));
        var stmt_else := Assign("x", Const(0));
        var stmt := If(cond_expr, stmt_then, stmt_else);
        var env := map[];
        var state := map[];

        AnalyzeProgramSound(stmt, env);

        assert AnalyzeStmt(stmt, state).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1;
        case Err(e1) => assert false;
    }

    method TestCase4(){
        /*
        if(1){
            x := 1;
        } else{
            y := 0;
        }
        z := x;
        */
        var cond_expr := Const(1);
        var stmt_then := Assign("x", Const(1));
        var stmt_else := Assign("y", Const(0));
        var if_stmt := If(cond_expr, stmt_then, stmt_else);
        var stmt := Seq(if_stmt, Assign("z", Var("x")));
        var env := map[];
        var state := map[];

        assert AnalyzeStmt(stmt, state).0;    
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["x"] == 1;
        case Err(e1) => assert false;
    }

    method TestCase5(){
        /*
        z := 1 / 0;
        */
        var stmt := Assign("z", Div(Const(1), Const(0)));
        var env := map[];
        var state := map[];

        assert !AnalyzeStmt(stmt, state).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert false;
        case Err(e1) => assert e1 == DivByZero();
    }

    method TestCase6(){
        /*
        z := 12 / (2 + 2);
        */
        var stmt := Assign("z", Div(Const(12), Add(Const(2), Const(2))));
        var env := map[];
        var state := map[];

        assert !AnalyzeStmt(stmt, state).0;
        
        match ExecStmt(stmt, env)
        case Ok(env1) => assert env1["z"] == 3;
        case Err(e1) => assert false;
    }

    method TestCase7(){
        /*
        if(1 + (-1)){
            v := 30;
        } else{
            v := 4 * 4;
            v := v - 2;
        }
        */
        var cond := Add(Const(1), Const(-1));
        var stmt1 := Assign("v", Mul(Const(4), Const(4)));
        var stmt2 := Assign("v", Sub(Var("v"), Const(2)));
        var stmt3 := If(cond, Assign("v", Const(30)), Seq(stmt1, stmt2));
        var state := map[];
        
        assert AnalyzeStmt(stmt3, state).0;
        var env := map[];
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 14;
        case Err(e1) => assert false;
    }

    method TestCase8(){
        /*
        v := 4 + 4;
        v := v % 2;
        */
        var stmt1 := Assign("v", Add(Const(4), Const(4)));
        var stmt2 := Assign("v", Mod(Var("v"), Const(2)));
        var stmt3 := Seq(stmt1, stmt2);
        var env := map[];
        var state := map[];
        
        AnalyzeProgramSound(stmt3, env);
        assert AnalyzeStmt(stmt3, state).0;
        match ExecStmt(stmt3, env)
        case Ok(env1) => assert env1["v"] == 0;
        case Err(e1) => assert false;
    }
}