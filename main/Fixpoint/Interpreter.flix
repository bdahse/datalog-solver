/*
 * Copyright 2021 Benjamin Dahse
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use Fixpoint/Ram.{Stmt, RelOp, RelSym, RamTerm, BoolExp, RowVar};

namespace Fixpoint {
    type alias Tuple[v] = List[v]
    type alias Database[v] = MutMap[RelSym, MutSet[Tuple[v]]]
    type alias SearchEnv[v] = Map[RowVar, Tuple[v]]

    pub def interpret[v : Order : Eq](stmt: Stmt[v]): Map[String, Set[List[v]]] & Impure =
        let db = MutMap.empty();
        db.evalStmt(stmt);
        ???

    def evalStmt[v : Order : Eq](db: Database[v], stmt: Stmt[v]): Unit & Impure = match stmt {
        case Stmt.Insert(relOp) => evalOp(db, Map#{}, relOp)
        case Stmt.Merge(src, dst) =>
            db |>
            MutMap.getOrElsePut!(dst, MutSet.empty()) |>
            MutSet.addAll!(MutMap.getWithDefault(src, MutSet.empty(), db))
        case Stmt.Assign(lhs, rhs) =>
            db |>
            MutMap.put!(lhs, MutMap.getWithDefault(rhs, MutSet.empty(), db))
        case Stmt.Purge(relSym) => MutMap.remove!(relSym, db)
        case Stmt.Seq(stmts) => List.foreach(evalStmt(db), stmts)
        case Stmt.While(test, body) =>
            if (evalBoolExp(db, Map#{}, test)) {
                evalStmt(db, body);
                evalStmt(db, stmt)
            } else {
                ()
            }
    }

    def evalOp[v : Order : Eq](db: Database[v], env: SearchEnv[v], op: RelOp[v]): Unit & Impure = match op {
        case RelOp.Search(rowVar, relSym, None, body) =>
            db |>
            MutMap.getWithDefault(relSym, MutSet.empty()) |>
            MutSet.foreach(row -> evalOp(db, Map.insert(rowVar, row, env), body))
        case RelOp.Search(rowVar, relSym, Some(searchCond), body) =>
            db |>
            MutMap.getWithDefault(relSym, MutSet.empty()) |>
            MutSet.foreach(row -> {
                let env = Map.insert(rowVar, row, env);
                if (evalBoolExp(db, env, searchCond)) {
                    evalOp(db, env, body)
                } else {
                    ()
                }
            })
        case RelOp.Project(terms, relSym) =>
            let tuple = List.map(evalTerm(env), terms);
            db |>
            MutMap.getOrElsePut!(relSym, MutSet.empty()) |>
            MutSet.add!(tuple)
    }

    def evalBoolExp[v : Order : Eq](db: Database[v], env: SearchEnv[v], exp: BoolExp[v]): Bool & Impure = match exp {
        case BoolExp.Empty(relSym) =>
            db |> MutMap.getWithDefault(relSym, MutSet.empty()) |> MutSet.isEmpty
        case BoolExp.MemberOf(terms, relSym) =>
            let tuple = List.map(evalTerm(env), terms);
            db |>
            MutMap.getWithDefault(relSym, MutSet.empty()) |>
            MutSet.memberOf(tuple)
        case BoolExp.Eq(lhs, rhs) =>
            evalTerm(env, lhs) == evalTerm(env, rhs)
        case BoolExp.Not(e) =>
            not evalBoolExp(db, env, e)
        case BoolExp.And(lhs, rhs) =>
            evalBoolExp(db, env, lhs) and evalBoolExp(db, env, rhs)
    }

    def evalTerm(env: SearchEnv[v], term: RamTerm[v]): v = match term {
        case RamTerm.Lit(v) => v
        case RamTerm.Attribute(rowVar, index) =>
            env |> Map.getWithDefault(rowVar, Nil) |> tupleGet(index)
    }

    def tupleGet(i: Int32, t: Tuple[v]): v = match (t, i) {
        case (v :: vs, 0) => v
        case (v :: vs, _) => tupleGet(i - 1, vs)
        case _ => ??? // Index out of bounds
    }
}