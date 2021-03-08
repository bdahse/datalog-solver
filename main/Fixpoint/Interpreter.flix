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

use Fixpoint/Ram.{RamStmt, RelOp, RelSym, RamTerm, BoolExp, RowVar};

namespace Fixpoint {
    type alias Tuple[v] = List[v]
    type alias Database[v] = MutMap[RelSym, MutSet[Tuple[v]]]
    type alias SearchEnv[v] = Map[RowVar, Tuple[v]]
    pub opaque type Model[v] = Map[String, Set[List[v]]]

    pub def interpret[v : Order : Eq](stmt: RamStmt[v]): Model[v] & Impure =
        let db = MutMap.empty();
        evalStmt(db, stmt);
        MutMap.foldLeftWithKey(acc -> k -> v -> match k {
            case RelSym.Full(relName) => Map.insert(relName, MutSet.toImmutable(v), acc)
            case _ => acc
        }, Map#{}, db) |>
        Model

    def evalStmt[v : Order : Eq](db: Database[v], stmt: RamStmt[v]): Unit & Impure = match stmt {
        case RamStmt.Insert(relOp) => evalOp(db, Map#{}, relOp)
        case RamStmt.Merge(src, dst) =>
            db |>
            MutMap.getOrElsePut!(dst, MutSet.empty()) |>
            MutSet.addAll!(MutMap.getWithDefault(src, MutSet.empty(), db))
        case RamStmt.Assign(lhs, rhs) =>
            db |>
            MutMap.put!(lhs, MutMap.getWithDefault(rhs, MutSet.empty(), db))
        case RamStmt.Purge(relSym) => MutMap.remove!(relSym, db)
        case RamStmt.Seq(stmts) => List.foreach(evalStmt(db), stmts)
        case RamStmt.While(test, body) =>
            if (evalBoolExp(db, Map#{}, test)) {
                evalStmt(db, body);
                evalStmt(db, stmt)
            } else {
                ()
            }
        case RamStmt.Comment(_) => ()
    }

    def evalOp[v : Order : Eq](db: Database[v], env: SearchEnv[v], op: RelOp[v]): Unit & Impure =
        match op {
            case RelOp.Search(rowVar, relSym, None, body) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.foreach(row -> evalOp(db, Map.insert(rowVar, row, env), body))
            case RelOp.Search(rowVar, relSym, Some(where), body) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.foreach(row -> {
                    let env = Map.insert(rowVar, row, env);
                    if (evalBoolExp(db, env, where)) {
                        evalOp(db, env, body)
                    } else {
                        ()
                    }
                })
            case RelOp.Query(rowVar, relSym, query, None, body) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.query(evalQuery(env, query)) |>
                List.foreach(row -> evalOp(db, Map.insert(rowVar, row, env), body))
            case RelOp.Query(rowVar, relSym, query, Some(where), body) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.query(evalQuery(env, query)) |>
                List.foreach(row -> {
                    let env = Map.insert(rowVar, row, env);
                    if (evalBoolExp(db, env, where)) {
                        evalOp(db, env, body)
                    } else {
                        ()
                    }
                })
            case RelOp.Project(terms, relSym) =>
                let tuple = List.map(evalTerm(env), terms);
                MutMap.getOrElsePut!(relSym, MutSet.empty(), db) |>
                MutSet.add!(tuple)
        }

    def evalQuery[v : Order](env: SearchEnv[v], query: List[RamTerm[v]], tuple: List[v]): Comparison =
        match (tuple, query) {
            case (_, Nil) => EqualTo
            case (v :: vs, t :: ts) => match v <=> evalTerm(env, t) {
                case EqualTo => evalQuery(env, ts, vs)
                case cmp => cmp
            }
            case _ => ??? // Impossible
        }

    def evalBoolExp[v : Order : Eq](db: Database[v], env: SearchEnv[v], exp: BoolExp[v]): Bool & Impure =
        match exp {
            case BoolExp.Empty(relSym) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |> MutSet.isEmpty
            case BoolExp.MemberOf(terms, relSym) =>
                let tuple = List.map(evalTerm(env), terms);
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.memberOf(tuple)
            case BoolExp.Guard(f, terms) =>
                List.map(evalTerm(env), terms) |> f
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
            Map.getWithDefault(rowVar, Nil, env) |> tupleGet(index)
        case RamTerm.App(f, args) =>
            List.map(evalTerm(env), args) |> f
    }

    def tupleGet(i: Int32, t: Tuple[v]): v = match (t, i) {
        case (v :: vs, 0) => v
        case (v :: vs, _) => tupleGet(i - 1, vs)
        case _ => ??? // Index out of bounds
    }

    instance ToString[Model[v]] with [v : ToString] {
        def toString(model: Model[v]): String = match model {
            case Model(db) =>
                let relations =
                    Map.mapWithKey(k -> v -> {
                        let relation =
                            Set.map(tuple -> match List.map(ToString.toString, tuple) {
                                case x :: Nil => x
                                case ts =>
                                    let xs = String.intercalate(", ", ts);
                                    "(${xs})"
                            }, v) |>
                            Set.toList |>
                            String.intercalate(", ");
                        "${k}#{${relation}}"
                    }, db) |>
                    Map.valuesOf |>
                    String.intercalate(", ");
                "Model#{${relations}}"
        }
    }
}