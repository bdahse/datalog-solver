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
    pub opaque type Tuple[v] = Array[v]
    type alias Database[v] = MutMap[RelSym, MutSet[Tuple[v]]]
    type alias SearchEnv[v] = Map[RowVar, Tuple[v]]
    pub opaque type Model[v] = Map[String, Set[Tuple[v]]]

    pub def interpret[v : Order : Eq](stmt: RamStmt[v]): Model[v] & Impure =
        let db = MutMap.empty();
        evalStmt(db, stmt);
        toModel(db)

    def toModel(db: Database[v]): Model[v] & Impure =
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
        case RamStmt.Until(test, body) =>
            if (List.forall(evalBoolExp(db, Map#{}) as BoolExp[v] -> Bool, test)) {
                ()
            } else {
                evalStmt(db, body);
                evalStmt(db, stmt)
            }
        case RamStmt.Comment(_) => ()
    }

    def evalOp[v : Order : Eq](db: Database[v], env: SearchEnv[v], op: RelOp[v]): Unit & Impure =
        match op {
            case RelOp.Search(rowVar, relSym, where, body) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.foreach(row -> {
                    let env = Map.insert(rowVar, row, env);
                    if (List.forall(evalBoolExp(db, env) as BoolExp[v] -> Bool, where)) {
                        evalOp(db, env, body)
                    } else {
                        ()
                    }
                })
            case RelOp.Query(rowVar, relSym, query, where, body) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |>
                MutSet.query(evalQuery(env, 0, query)) |>
                List.foreach(row -> {
                    let env = Map.insert(rowVar, row, env);
                    if (List.forall(evalBoolExp(db, env) as BoolExp[v] -> Bool, where)) {
                        evalOp(db, env, body)
                    } else {
                        ()
                    }
                })
            case RelOp.Project(terms, relSym) =>
                let tuple = Tuple(Array.map(evalTerm(env), terms));
                MutMap.getOrElsePut!(relSym, MutSet.empty(), db) |>
                MutSet.add!(tuple)
        }

    def evalQuery[v : Order](env: SearchEnv[v], i: Int32, query: Array[RamTerm[v]], tuple: Tuple[v]): Comparison =
        let Tuple(t) = tuple;
        if (i >= Array.length(query))
            EqualTo
        else match (t[i] as & Pure) <=> evalTerm(env, query[i] as & Pure) {
            case EqualTo => evalQuery(env, i+1, query, tuple)
            case cmp => cmp
        }

    def evalBoolExp[v : Order : Eq](db: Database[v], env: SearchEnv[v], exp: BoolExp[v]): Bool & Impure =
        match exp {
            case BoolExp.Empty(relSym) =>
                MutMap.getWithDefault(relSym, MutSet.empty(), db) |> MutSet.isEmpty
            case BoolExp.NotMemberOf(terms, relSym) => match MutMap.get(relSym, db) {
                case Some(table) =>
                    let tuple = Tuple(Array.map(evalTerm(env), terms));
                    not MutSet.memberOf(tuple, table)
                case None => true
            }
            case BoolExp.Guard(f, terms) =>
                List.map(evalTerm(env), terms) |> f
            case BoolExp.Eq(lhs, rhs) =>
                evalTerm(env, lhs) == evalTerm(env, rhs)
        }

    def evalTerm(env: SearchEnv[v], term: RamTerm[v]): v = match term {
        case RamTerm.Lit(v) => v
        case RamTerm.Attribute(rowVar, index) =>
            let Tuple(tuple) = Map.getWithDefault(rowVar, Tuple([] as & Pure), env);
            tuple[index] as & Pure
        case RamTerm.App(f, args) =>
            List.map(evalTerm(env), args) |> f
    }

    instance Order[Tuple[v]] with [v : Order] {
        pub def less(a: Tuple[v], b: Tuple[v]): Bool = match a <=> b {
            case LessThan => true
            case _ => false
        }

        pub def lessEqual(a: Tuple[v], b: Tuple[v]): Bool = match a <=> b {
            case LessThan => true
            case EqualTo => true
            case _ => false
        }

        pub def greater(a: Tuple[v], b: Tuple[v]): Bool = match a <=> b {
            case GreaterThan => true
            case _ => false
        }

        pub def greaterEqual(a: Tuple[v], b: Tuple[v]): Bool = match a <=> b {
            case GreaterThan => true
            case EqualTo => true
            case _ => false
        }

        pub def compare(a: Tuple[v], b: Tuple[v]): Comparison = match (a, b) {
            case (Tuple(a), Tuple(b)) => compareHelper(a, b, 0) as & Pure
        }
    }

    // Unused def. unless this is public. Bug?
    pub def compareHelper[v : Order](a: Array[v], b: Array[v], i: Int32): Comparison & Impure =
        let alen = Array.length(a);
        let blen = Array.length(b);
        if (i >= alen and i >= blen)
            EqualTo
        else if (i >= alen)
            LessThan
        else if (i >= blen)
            GreaterThan
        else match a[i] <=> b[i] {
            case EqualTo => compareHelper(a, b, i+1)
            case cmp => cmp
        }

    instance ToString[Model[v]] with [v : ToString] {
        def toString(model: Model[v]): String = match model {
            case Model(db) =>
                let relations =
                    Map.mapWithKey(k -> v -> {
                        let relation =
                            Set.map(match Tuple(tuple) ->
                            match List.map(ToString.toString, Array.toList(tuple) as & Pure) {
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