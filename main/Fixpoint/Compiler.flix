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

namespace Fixpoint/Ast {
    pub def compile(cs: List[Constraint[v]], strat: Map[PredSym, Int32]): RamStmt[v] =
        let facts = cs |> facts |> List.map(compileRule(-1)) |> List.fold;
        let strata =
            strat |>
            Map.invert |>
            Map.map(restrict(cs) >> compileStratum) |>
            Map.valuesOf |>
            List.fold;
        List.fold(facts :: strata :: Nil)

    def compileStratum(stratum: List[Constraint[v]]): RamStmt[v] =
        let idb = stratum |> idb |> Set.toList;
        let init = stratum |> List.map(compileRule(-1)) |> List.fold;
        let mergeDelta =
            idb |>
            List.map(match PredSym(relName, _) ->
                RamStmt.Merge(RelSym.New(relName), RelSym.Delta(relName))
            ) |>
            List.fold;
        let mergeFull =
            idb |>
            List.map(match PredSym(relName, _) ->
                RamStmt.Merge(RelSym.New(relName), RelSym.Full(relName))
            ) |>
            List.fold;
        let eval = stratum |> List.map(compileRuleIncr) |> List.fold;
        let mergeNew =
            idb |>
            List.map(match PredSym(relName, _) ->
                RamStmt.Merge(RelSym.New(relName), RelSym.Full(relName))
            ) |>
            List.fold;
        let assign =
            idb |>
            List.map(match PredSym(relName, _) ->
                RamStmt.Assign(RelSym.Delta(relName), RelSym.New(relName))
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
        let fixpoint = RamStmt.While(unwrap(whileTest), whileBody);
        List.fold(init :: mergeDelta :: mergeFull :: fixpoint :: Nil)

    /// Compile rule into a join loop where delta designates the focused atom.
    def compileRule(delta: Int32, rule: Constraint[v]): RamStmt[v] = match rule {
        case Constraint(_, HeadAtom(PredSym(headPred, _), headTerms, _), body, _) =>
            let env = unifyVars(body);
            let join = joinTerms(env, body);
            let ramTerms = List.map(compileHeadTerm(env), headTerms);
            let projection = RelOp.Project(ramTerms, RelSym.New(headPred));
            List.mapWithIndex(atom -> i -> (atom, i), body) |>
            List.foldRight2(rowVar -> match (atom, i) -> match (isLast, acc) -> match atom {
                case BodyAtom(_, Negative, _, _) => (false, acc)
                case BodyAtom(PredSym(pred, _), Positive, _, _) =>
                    let relSym = if (i == delta) {
                        RelSym.Delta(pred)
                    } else {
                        RelSym.Full(pred)
                    };
                    let searchCond = if (isLast) {
                        join |>
                        Option.map(lhs -> BoolExp.And(lhs, BoolExp.Not(BoolExp.MemberOf(ramTerms, RelSym.Full(headPred)))))
                    } else {
                        None
                    };
                    (false, RelOp.Search(rowVar, relSym, searchCond, acc))
            }, (true, projection), rowVars(body)) |>
            snd |>
            RamStmt.Insert
    }

    def compileRuleIncr(rule: Constraint[v]): RamStmt[v] = match rule {
        case Constraint(_, _, body, _) =>
            body |> List.mapWithIndex(_ -> i -> compileRule(i, rule)) |> List.fold
    }

    def compileHeadTerm(env: Map[VarSym, RamTerm[v]], term: HeadTerm[v]): RamTerm[v] = match term {
        case HeadTerm.Var(var, _) => env |> Map.get(var) |> unwrap
        case HeadTerm.Lit(v, _) => RamTerm.Lit(v)
        case HeadTerm.App(_, _, _) => ??? // TODO: How to handle this?
    }

    def compileBodyTerm(env: Map[VarSym, RamTerm[v]], term: BodyTerm[v]): RamTerm[v] = match term {
        case BodyTerm.Var(var, _) => env |> Map.get(var) |> unwrap
        case BodyTerm.Lit(v, _) => RamTerm.Lit(v)
    }

    def rowVars(body: List[BodyPredicate[v]]): List[RowVar] =
        List.mapWithIndex(match BodyAtom(PredSym(pred, _), _, _, _) -> i -> {
            RowVar.Named(pred + "$" + ToString.toString(i))
        }, body)

    /// Unifies each variable that occurs in a rule body with an attribute
    /// corresponding to a positive atom where the variable is a term.
    def unifyVars(body: List[BodyPredicate[v]]): Map[VarSym, RamTerm[v]] =
        List.foldLeft2(acc -> atom -> rowVar -> match atom {
            case BodyAtom(_, Negative, _, _) => acc
            case BodyAtom(_, Positive, terms, _) =>
                List.mapWithIndex(term -> j -> match term {
                    case BodyTerm.Var(var, _) => Map.singleton(var, RamTerm.Attribute(rowVar, j))
                    case BodyTerm.Lit(_, _) => Map#{}
                }, terms) |>
                List.foldLeft(Map.union, acc)
        }, Map#{}, body, rowVars(body))

    /// Equates every term in a positive body atom with an attribute
    /// and declares that terms in negative body atoms are not in the corresponding relations.
    def joinTerms(env: Map[VarSym, RamTerm[v]], body: List[BodyPredicate[v]]): Option[BoolExp[v]] =
        List.flatMap2(atom -> rowVar -> match atom {
            case BodyAtom(_, Positive, terms, _) =>
                List.mapWithIndex(term -> j -> {
                    let ramTerm = compileBodyTerm(env, term);
                    BoolExp.Eq(ramTerm, RamTerm.Attribute(rowVar, j))
                }, terms)
            case BodyAtom(PredSym(relName, _), Negative, terms, _) =>
                let ramTerms = List.map(compileBodyTerm(env), terms);
                BoolExp.Not(BoolExp.MemberOf(ramTerms, RelSym.Full(relName))) :: Nil
        }, body, rowVars(body)) |>
        List.reduceLeft(lhs -> rhs -> BoolExp.And(lhs, rhs))

    def unwrap(o: Option[a]): a = match o {
        case Some(a) => a
        case None => ???
    }

    /// Restrict a constraint system to those rules whose head predicate belongs to a given domain.
    def restrict(cs: List[Constraint[v]], domain: Set[PredSym]): List[Constraint[v]] =
        let headPred = match Constraint(_, HeadAtom(headSym, _, _), _, _) -> headSym;
        let memberOf = xs -> x -> Set.memberOf(x, xs);
        List.filter(headPred >> memberOf(domain), cs)

    def idb(cs: List[Constraint[v]]): Set[PredSym] =
        let headPred = acc -> c -> match c {
            case Constraint(_, _, Nil, _) => acc
            case Constraint(_, HeadAtom(headSym, _, _), _, _) => Set.insert(headSym, acc)
        };
        List.foldLeft(headPred, Set#{}, cs)

    def facts(cs: List[Constraint[v]]): List[Constraint[v]] =
        let body = match Constraint(_, _, atoms, _) -> atoms;
        List.filter(body >> List.isEmpty, cs)
}