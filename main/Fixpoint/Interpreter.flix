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

use Fixpoint/Ram.{Stmt, RelOp, RelSym, RamTerm, BoolExp};

namespace Fixpoint {
    type alias Database[v] = MutMap[RelSym, MutSet[List[v]]]

    pub def interpret[v : Order : Eq](stmt: Stmt[v]): Map[String, Set[List[v]]] & Impure =
        let db = MutMap.empty();
        db.evalStmt(stmt);
        ???

    def evalStmt[v : Order : Eq](db: Database[v], stmt: Stmt[v]): Unit & Impure =
        let eval = evalStmt(db);
        match stmt {
            case Stmt.Insert(relOp) => db.evalOp(relOp)
            case Stmt.Merge(src, dst) =>
                db |>
                MutMap.getOrElsePut!(dst, MutSet.empty()) |>
                MutSet.addAll!(db |> MutMap.getWithDefault(src, MutSet.empty()))
            case Stmt.Swap(rel1, rel2) => ???
            case Stmt.Purge(relSym) => db |> MutMap.remove!(relSym)
            case Stmt.Seq(stmts) => stmts |> List.foreach(eval)
            case Stmt.While(test, body) =>
                if (db.evalBoolExp(test)) {
                    body.eval();
                    stmt.eval()
                } else {
                    ()
                }
        }

    def evalOp[v : Order](db: Database[v], op: RelOp[v]): Unit & Impure =
        let eval = evalOp(db);
        match op {
            case RelOp.Search(relName, searchCond, body) => ???
            case RelOp.Project(tuple, relSym) =>
                db |>
                MutMap.getOrElsePut!(relSym, MutSet.empty()) |>
                MutSet.add!(tuple |> List.map(evalTerm(db)))
        }

    def evalBoolExp[v : Eq : Order](db: Database[v], exp: BoolExp[v]): Bool & Impure =
        let eval = evalBoolExp(db);
        match exp {
            case BoolExp.Empty(relSym) =>
                db |> MutMap.getWithDefault(relSym, MutSet.empty()) |> MutSet.isEmpty
            case BoolExp.MemberOf(tuple, relSym) =>
                db |>
                MutMap.getWithDefault(relSym, MutSet.empty()) |>
                MutSet.memberOf(tuple |> List.map(evalTerm(db)))
            case BoolExp.Eq(lhs, rhs) => db.evalTerm(lhs) == db.evalTerm(rhs)
            case BoolExp.Not(e) => not e.eval()
            case BoolExp.And(lhs, rhs) => lhs.eval() and rhs.eval()
        }

    def evalTerm(db: Database[v], term: RamTerm[v]): v = ???
}