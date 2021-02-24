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

namespace Fixpoint/Ast {
    pub def compile(cs: List[Constraint[v]], strat: Map[PredSym, Int32]): Stmt[v] =
        let facts = cs |> facts |> List.map(compileRule) |> List.fold;
        let strata =
            strat |>
            Map.invert |>
            Map.map(restrict(cs) >> compileStratum) |>
            Map.valuesOf |>
            List.fold;
        List.fold(facts :: strata :: Nil)

    def compileStratum(stratum: List[Constraint[v]]): Stmt[v] =
        let idb = stratum |> idb |> Set.toList;
        let init = stratum |> List.map(compileRule) |> List.fold;
        let mergeDelta =
            idb |>
            List.map(match PredSym(relName, _) ->
                Stmt.Merge(RelSym.Full(relName), RelSym.Delta(relName))
            ) |>
            List.fold;
        let eval = stratum |> List.map(compileRuleIncr) |> List.fold;
        let mergeNew =
            idb |>
            List.map(match PredSym(relName, _) ->
                Stmt.Merge(RelSym.New(relName), RelSym.Full(relName))
            ) |>
            List.fold;
        let assign =
            idb |>
            List.map(match PredSym(relName, _) ->
                Stmt.Assign(RelSym.Delta(relName), RelSym.New(relName))
            ) |>
            List.fold;
        let whileTest =
            idb |>
            List.map(match PredSym(relName, _) ->
                BoolExp.Empty(RelSym.Delta(relName))
            ) |>
            List.reduceLeft(lhs -> rhs -> BoolExp.And(lhs, rhs)) |>
            Option.map(BoolExp.Not);
        let whileBody = List.fold(eval :: mergeNew :: assign :: Nil);
        let fixpoint = Stmt.While(whileTest |> unwrap, whileBody);
        List.fold(init :: mergeDelta :: fixpoint :: Nil)

    def compileRule(rule: Constraint[v]): Stmt[v] = match rule {
        case Constraint(_, HeadAtom(PredSym(headPred, _), headTerms, _), body, _) =>
            let env = unifyVars(body);
            let join  = joinTerms(env, body);
            let ramTerms = List.map(compileHeadTerm(env), headTerms);
            let projection = RelOp.Project(ramTerms, RelSym.Full(headPred));
            let search =
                body |>
                List.zip(rowVars(body)) |>
                List.last |>
                Option.flatMap(match (rowVar, atom) -> match atom {
                    case BodyAtom(PredSym(pred, _), Positive, _, _) =>
                        Some(RelOp.Search(rowVar, RelSym.Full(pred), join, projection))
                    case BodyAtom(_, Negative, _, _) => None
                }) |>
                Option.flatMap(innerSearch ->
                    body |>
                    List.zip(rowVars(body)) |>
                    List.init |>
                    Option.map(List.foldRight(match (rowVar, atom) -> acc -> match atom {
                        case BodyAtom(PredSym(pred, _), Positive, _, _) =>
                            RelOp.Search(rowVar, RelSym.Full(pred), None, acc)
                        case BodyAtom(_, Negative, _, _) => acc
                    }, innerSearch)));
            Stmt.Insert(projection |> Option.getWithDefault(search))
    }

    def compileRuleIncr(rule: Constraint[v]): Stmt[v] =
        let compile = delta -> match rule {
            case Constraint(_, HeadAtom(PredSym(headPred, _), headTerms, _), body, _) =>
                let env = unifyVars(body);
                let join = joinTerms(env, body);
                let ramTerms = List.map(compileHeadTerm(env), headTerms);
                let projection = RelOp.Project(ramTerms, RelSym.New(headPred));
                let searchCond =
                    join |>
                    Option.map(cond ->
                        BoolExp.And(cond,
                                    BoolExp.Not(BoolExp.MemberOf(ramTerms, RelSym.Full(headPred)))));
                let search =
                    body |>
                    List.zip(rowVars(body)) |>
                    List.mapWithIndex(match (rowVar, atom) -> i -> (atom, i, rowVar)) |>
                    List.last |>
                    Option.flatMap(match (atom, i, rowVar) -> match atom {
                        case BodyAtom(PredSym(pred, _), Positive, _, _) =>
                            let relSym = if (i == delta) {
                                RelSym.Delta(pred)
                            } else {
                                RelSym.Full(pred)
                            };
                            Some(RelOp.Search(rowVar, relSym, searchCond, projection))
                        case BodyAtom(_, Negative, _, _) => None
                    }) |>
                    Option.flatMap(innerSearch ->
                        body |>
                        List.zip(rowVars(body)) |>
                        List.mapWithIndex(match (rowVar, atom) -> i -> (atom, i, rowVar)) |>
                        List.init |>
                        Option.map(List.foldRight(match (atom, i, rowVar) -> acc -> match atom {
                            case BodyAtom(PredSym(pred, _), Positive, _, _) =>
                                let relSym = if (i == delta) {
                                    RelSym.Delta(pred)
                                } else {
                                    RelSym.Full(pred)
                                };
                                RelOp.Search(rowVar, relSym, None, acc)
                            case BodyAtom(_, Negative, _, _) => acc
                        }, innerSearch)));
                Stmt.Insert(unwrap(search))
        };
        match rule {
            case Constraint(_, _, body, _) =>
                body |> List.mapWithIndex(_ -> i -> compile(i)) |> List.fold
        }

    def compileHeadTerm(env: Map[VarSym, RamTerm[v]], term: HeadTerm[v]): RamTerm[v] = match term {
        case HeadTerm.Var(var, _) => env |> Map.get(var) |> unwrap
        case HeadTerm.Lit(v, _) => RamTerm.Lit(v)
        case HeadTerm.App(_, _, _) => ??? // TODO: How to handle this?
    }

    def compileBodyTerm(env: Map[VarSym, RamTerm[v]], term: BodyTerm[v]): RamTerm[v] = match term {
        case BodyVar(var, _) => env |> Map.get(var) |> unwrap
        case BodyLit(v, _) => RamTerm.Lit(v)
    }

    def rowVars(body: List[BodyPredicate[v]]): List[RowVar] =
        List.mapWithIndex(match BodyAtom(PredSym(pred, _), _, _, _) -> i -> {
            RowVar.Named(pred + "$" + ToString.toString(i))
        }, body)

    /// Unifies each variable that occurs in a rule body with an attribute
    /// corresponding to a positive atom where the variable is a term.
    def unifyVars(body: List[BodyPredicate[v]]): Map[VarSym, RamTerm[v]] =
        body |>
        rowVars |>
        List.flatMap2(atom -> rowVar -> match atom {
            case BodyAtom(_, Positive, terms, _) =>
                List.mapWithIndex(term -> j -> match term {
                    case BodyVar(var, _) => Map.singleton(var, RamTerm.Attribute(rowVar, j))
                    case BodyLit(_, _) => Map#{}
                }, terms)
            case BodyAtom(_, Negative, _, _) => Map#{} :: Nil
        }, body) |>
        List.foldLeft(Map.union, Map#{})

    /// Equates every term in a positive body atom with an attribute
    /// and declares that terms in negative body atoms are not in the corresponding relations.
    def joinTerms(env: Map[VarSym, RamTerm[v]], body: List[BodyPredicate[v]]): Option[BoolExp[v]] =
        body |>
        rowVars |>
        List.flatMap2(atom -> rowVar -> match atom {
            case BodyAtom(_, Positive, terms, _) =>
                List.mapWithIndex(term -> j -> {
                    let ramTerm = compileBodyTerm(env, term);
                    BoolExp.Eq(ramTerm, RamTerm.Attribute(rowVar, j))
                }, terms)
            case BodyAtom(PredSym(relName, _), Negative, terms, _) =>
                let ramTerms = List.map(compileBodyTerm(env), terms);
                BoolExp.Not(BoolExp.MemberOf(ramTerms, RelSym.Full(relName))) :: Nil
        }, body) |>
        List.reduceLeft(lhs -> rhs -> BoolExp.And(lhs, rhs))

    def unwrap(o: Option[a]): a = match o {
        case Some(a) => a
        case None => ???
    }

    def restrict(cs: List[Constraint[v]], domain: Set[PredSym]): List[Constraint[v]] =
        let headPred = match Constraint(_, HeadAtom(headSym, _, _), _, _) -> headSym;
        let memberOf = xs -> x -> Set.memberOf(x, xs);
        cs |> List.filter(headPred >> memberOf(domain))

    def idb(cs: List[Constraint[v]]): Set[PredSym] =
        let headPred = acc -> c -> match c {
            case Constraint(_, _, Nil, _) => acc
            case Constraint(_, HeadAtom(headSym, _, _), _, _) => acc |> Set.insert(headSym)
        };
        cs |> List.foldLeft(headPred, Set#{})

    def facts(cs: List[Constraint[v]]): List[Constraint[v]] =
        let body = match Constraint(_, _, atoms, _) -> atoms;
        cs |> List.filter(body >> List.isEmpty)
}