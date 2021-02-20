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

use Fixpoint/Ram.{Stmt, RelOp, RelSym, RamTerm};

namespace Fixpoint/Ast {
    def _compile(cs: List[Constraint[v]], strat: Map[PredSym, Int32]): Stmt[v] =
        let facts = cs.compileFacts();
        let strata = cs.compileStrata(strat);
        List.fold(facts :: strata :: Nil)

    def compileFacts(cs: List[Constraint[v]]): Stmt[v] =
        let toRam = term -> match term {
            case HeadTerm.Var(_, _) => ??? // Impossible
            case HeadTerm.Lit(v, _) => RamTerm.Lit(v)
            case HeadTerm.App(_, _, _) => ??? // TODO: how to handle this?
        };
        let compile = fact -> match fact {
            case Constraint(_, HeadAtom(PredSym(sym, _), terms, _), _, _) =>
                Stmt.Insert(RelOp.Project(terms |> List.map(toRam), RelSym.Full(sym)))
        };
        cs.facts() |> List.map(compile) |> List.fold

    def compileStrata(cs: List[Constraint[v]], strat: Map[PredSym, Int32]): Stmt[v] =
        let invertMap = acc -> k -> v -> Map.insertWith(Set.union, v, Set#{k}, acc);
        let evalRule = stratum -> rule -> ???;
        let compile = stratum -> cs.restrict(stratum) |> List.map(evalRule(stratum)) |> List.fold;
        strat |>
        Map.foldWithKey(invertMap, Map#{}) |>
        Map.map(compile) |>
        Map.valuesOf |>
        List.fold

    def restrict(cs: List[Constraint[v]], domain: Set[PredSym]): List[Constraint[v]] =
        let headSym = c -> match c {
            case Constraint(_, HeadAtom(headPred, _, _), _, _) => headPred
        };
        let memberOf = xs -> x -> Set.memberOf(x, xs);
        cs |> List.filter(headSym >> memberOf(domain))

    def facts(cs: List[Constraint[v]]): List[Constraint[v]] =
        let isFact = c -> match c {
            case Constraint(Nil, _, Nil, _) => true
            case _ => false
        };
        cs |> List.filter(isFact)
}