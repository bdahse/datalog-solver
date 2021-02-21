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

namespace Fixpoint/Ast {
    def _compile(cs: List[Constraint[v]], strat: Map[PredSym, Int32]): Stmt[v] =
        let facts = cs.compileFacts();
        let strata = cs.compileStrata(strat);
        List.fold(facts :: strata :: Nil)

    def compileFacts(cs: List[Constraint[v]]): Stmt[v] =
        let toRam = termToRam(Map#{});
        let compile = fact -> match fact {
            case Constraint(_, HeadAtom(PredSym(headPred, _), terms, _), _, _) =>
                Stmt.Insert(RelOp.Project(terms |> List.map(toRam), RelSym.Full(headPred)))
        };
        cs.facts() |> List.map(compile) |> List.fold

    def compileStrata(cs: List[Constraint[v]]): Map[PredSym, Int32] -> Stmt[v] =
        let invertMap = acc -> k -> v -> Map.insertWith(Set.union, v, Set#{k}, acc);
        let unifyVars =
            List.mapWithIndex(atom -> i -> match atom {
                case BodyAtom(_, _, terms, _) => terms |> List.mapWithIndex(term -> j -> match term {
                    case BodyVar(var, _) => Map.singleton(var, RamTerm.Attribute(i, j))
                    case BodyLit(_, _) => Map#{}
            })}) >>
            List.flatten >>
            List.foldLeft(Map.union, Map#{});
        let joinTerms = env -> {
            let toRam = term -> match term {
                case BodyVar(var, _) => env |> Map.get(var) |> unwrap
                case BodyLit(v, _) => RamTerm.Lit(v)
            };
            List.mapWithIndex(atom -> i -> match atom {
                case BodyAtom(_, _, terms, _) =>
                    terms |> List.mapWithIndex(term -> j -> BoolExp.Eq(term.toRam(), RamTerm.Attribute(i, j)))
            }) >>
            List.flatten >>
            List.reduceLeft(lhs -> rhs -> BoolExp.And(lhs, rhs))
        };
        let evalRule = rule -> match rule {
            case Constraint(_, HeadAtom(PredSym(headPred, _), headTerms, _), body, _) =>
                let toRam = termToRam(body.unifyVars());
                let join = joinTerms(body.unifyVars());
                let projection = RelOp.Project(headTerms |> List.map(toRam), RelSym.Full(headPred));
                let search =
                    body |>
                    List.last |>
                    Option.map(atom -> match atom {
                        case BodyAtom(PredSym(pred, _), _, _, _) => RelOp.Search(RelSym.Full(pred), body.join(), projection)
                    }) |>
                    Option.flatMap(innerSearch ->
                        body |>
                        List.init |>
                        Option.flatMap(Option.foldRightM(atom -> acc -> match atom {
                            case BodyAtom(PredSym(pred, _), _, _, _) =>
                                Some(RelOp.Search(RelSym.Full(pred), None, acc))
                        }, innerSearch)));
                Stmt.Insert(projection |> Option.getWithDefault(search))
        };
        let compile = stratum -> cs.restrict(stratum) |> List.map(evalRule) |> List.fold;
        Map.foldWithKey(invertMap, Map#{}) >>
        Map.map(compile) >>
        Map.valuesOf >>
        List.fold

    def termToRam(env: Map[VarSym, RamTerm[v]], term: HeadTerm[v]): RamTerm[v] = match term {
        case HeadTerm.Var(var, _) => env |> Map.get(var) |> unwrap
        case HeadTerm.Lit(v, _) => RamTerm.Lit(v)
        case HeadTerm.App(_, _, _) => ??? // TODO: How to handle this?
    }

    def unwrap(o: Option[a]): a = match o {
        case Some(a) => a
        case None => ???
    }

    def restrict(cs: List[Constraint[v]], domain: Set[PredSym]): List[Constraint[v]] =
        let headPred = c -> match c {
            case Constraint(_, HeadAtom(headSym, _, _), _, _) => headSym
        };
        let memberOf = xs -> x -> Set.memberOf(x, xs);
        cs |> List.filter(headPred >> memberOf(domain))

    def facts(cs: List[Constraint[v]]): List[Constraint[v]] =
        let body = c -> match c {
            case Constraint(_, _, atoms, _) => atoms
        };
        cs |> List.filter(body >> List.isEmpty)
}