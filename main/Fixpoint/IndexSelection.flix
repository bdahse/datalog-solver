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

/// The purpose of this phase is to:
/// 1) Hoist inner search conditions to outer search conditions.
/// 2) Rewrite searches on relations to queries on indices, when possible.
/// It is possible to rewrite a search when it searches on attributes that form a prefix
/// of the attribute sequence used to lexicographically define the index.
/// Consider the following example:
/// search x ∈ b do
///     search (y, z, w) ∈ r do
///         search u ∈ c where
///             x = y /\ x = w /\ z = u /\ x ∉ a
///         do
///             project x into a
/// After step 1:
/// search x ∈ b where x ∉ a
/// do
///     search (y, z, w) ∈ r where x = y /\ x = w
///     do
///         search u ∈ c where z = u
///         do
///             project x into a
/// After step 2:
/// search x ∈ b where x ∉ a
/// do
///     query (y, z, w) ∈ {(y, z, w) ∈ r | x = y} where x = w
///     do
///         query u ∈ {u ∈ c | z = u}
///         do
///             project x into a
namespace Fixpoint {
    pub def hoistStmt(stmt: RamStmt[v]): RamStmt[v] = match stmt {
        case RamStmt.Insert(op) => hoistOp(op, Set#{}) |> fst |> RamStmt.Insert
        case RamStmt.Merge(_, _) => stmt
        case RamStmt.Assign(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Seq(xs) => RamStmt.Seq(List.map(hoistStmt, xs))
        case RamStmt.While(test, body) => RamStmt.While(test, hoistStmt(body))
        case RamStmt.Comment(_) => stmt
    }

    def hoistOp(op: RelOp[v], freeVars: Set[RowVar]): (RelOp[v], List[BoolExp[v]]) = match op {
        case RelOp.Search(var, relSym, None, body) =>
            let (innerOp, innerGround) = hoistOp(body, Set.insert(var, freeVars));
            let (ground, rest) = List.partition(isExpGround(freeVars), innerGround);
            let where = List.reduceLeft(lhs -> rhs -> BoolExp.And(rhs, lhs), rest);
            let search = RelOp.Search(var, relSym, where, innerOp);
            (search, ground)
        case RelOp.Search(var, relSym, Some(where), body) =>
            let (ground, rest) = flattenBoolExp(where) |> List.partition(isExpGround(freeVars));
            let where = List.reduceLeft(lhs -> rhs -> BoolExp.And(rhs, lhs), rest);
            let search = RelOp.Search(var, relSym, where, body);
            (search, ground)
        case RelOp.Query(_, _, _, _, _) => (op, Nil)
        case RelOp.Project(_, _) => (op, Nil)
    }

    pub def queryStmt[v : ToString](stmt: RamStmt[v]): RamStmt[v] = match stmt {
        case RamStmt.Insert(op) => RamStmt.Insert(queryOp(op))
        case RamStmt.Merge(_, _) => stmt
        case RamStmt.Assign(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Seq(xs) => RamStmt.Seq(List.map(queryStmt, xs))
        case RamStmt.While(test, body) => RamStmt.While(test, queryStmt(body))
        case RamStmt.Comment(_) => stmt
    }

    def queryOp[v : ToString](op: RelOp[v]): RelOp[v] = match op {
        case RelOp.Search(var, relSym, None, body) => RelOp.Search(var, relSym, None, queryOp(body))
        case RelOp.Search(var, relSym, Some(where), body) =>
            let varEqs =
                flattenBoolExp(where) |>
                List.filter(exp -> match exp {
                    case BoolExp.Eq(RamTerm.Attribute(row1, _), RamTerm.Attribute(row2, _)) =>
                        row1 != row2 and row1 == var
                    case BoolExp.Eq(RamTerm.Attribute(row, _), RamTerm.Lit(_)) => row == var
                    case _ => false
                });
            let rangeQuery =
                List.unfold(i -> {
                    List.findMap(eq -> match eq {
                        case BoolExp.Eq(RamTerm.Attribute(_, index), rhs) =>
                            if (i == index) {
                                Some(rhs)
                            } else {
                                None
                            }
                        case _ => None
                    }, varEqs) |>
                    Option.map(term -> (term, i + 1))
                }, 0);
            if (List.isEmpty(rangeQuery))
                RelOp.Search(var, relSym, Some(where), queryOp(body))
            else
                RelOp.Query(var, relSym, rangeQuery, Some(where), queryOp(body))
        case RelOp.Query(_, _, _, _, _) => op
        case RelOp.Project(_, _) => op
    }

    /// Return a list of expressions e1 :: e2 :: ... :: en :: Nil such that
    /// e1 /\ e2 /\ .... /\ en <=> exp.
    def flattenBoolExp(exp: BoolExp[v]): List[BoolExp[v]] = flattenHelper(exp, Nil)

    def flattenHelper(exp: BoolExp[v], acc: List[BoolExp[v]]): List[BoolExp[v]] = match exp {
        case BoolExp.Empty(_) => exp :: acc
        case BoolExp.MemberOf(_, _) => exp :: acc
        case BoolExp.Guard(_, _) => exp :: acc
        case BoolExp.Eq(_, _) => exp :: acc
        case BoolExp.Not(_) => exp :: acc
        case BoolExp.And(lhs, rhs) => flattenHelper(lhs, acc) |> flattenHelper(rhs)
    }

    /// An expression is ground if all its terms are ground.
    def isExpGround(freeVars: Set[RowVar], exp: BoolExp[v]): Bool = match exp {
        case BoolExp.Empty(_) => true
        case BoolExp.MemberOf(terms, _) => List.forall(isTermGround(freeVars), terms)
        case BoolExp.Guard(_, terms) => List.forall(isTermGround(freeVars), terms)
        case BoolExp.Eq(lhs, rhs) => isTermGround(freeVars, lhs) and isTermGround(freeVars, rhs)
        case BoolExp.Not(e) => isExpGround(freeVars, e)
        case BoolExp.And(lhs, rhs) => isExpGround(freeVars, lhs) and isExpGround(freeVars, rhs)
    }

    /// A term is ground if it is a literal or a free variable.
    def isTermGround(freeVars: Set[RowVar], term: RamTerm[v]): Bool = match term {
        case RamTerm.Lit(_) => true
        case RamTerm.Attribute(var, _) => Set.memberOf(var, freeVars)
        case RamTerm.App(_, args) => List.forall(isTermGround(freeVars), args)
    }
}