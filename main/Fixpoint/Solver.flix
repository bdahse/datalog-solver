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

namespace Fixpoint/Ast {

    pub def isRangeRestricted(cs: List[Constraint[v]]): Bool =
        List.forall(c -> match c {
            case Constraint(_, head, body, _) => headVars(head) `Set.isSubsetOf` bodyVars(body)
        }, cs)

    pub def nonPositivelyBoundVar(cs: List[Constraint[v]]): Bool =
        List.forall(c -> match c {
            case Constraint(_, _, body, _) => match polarityVars(body) {
                case (positive, negative)  => negative `Set.isSubsetOf` positive
            }
        }, cs)

    pub def foo() : List[Constraint[String]] =
        /// Rich("Magnus").
        /// Age(34).
        /// Rich("Joakim").
        /// Famous("Joakim").
        /// Happy(person) :- Rich(person), Famous(person).
        // TODO: Find out how to make this a testcase.
        let fact1 = Constraint(Nil, HeadAtom(PredSym("Rich", Unknown),
                                             HeadTerm.Lit("Magnus", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let fact2 = Constraint(Nil, HeadAtom(PredSym("Age", Unknown),
                                             HeadTerm.Lit("34", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let fact3 = Constraint(Nil, HeadAtom(PredSym("Rich", Unknown),
                                             HeadTerm.Lit("Joakim", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let fact4 = Constraint(Nil, HeadAtom(PredSym("Famous", Unknown),
                                             HeadTerm.Lit("Joakim", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let rule1 = Constraint(VarSym("person", Unknown) :: Nil,
                               HeadAtom(PredSym("Happy", Unknown),
                                        HeadTerm.Var(VarSym("person", Unknown), Unknown) :: Nil,
                                        Unknown),
                               BodyAtom(PredSym("Rich", Unknown),
                                        Positive,
                                        BodyVar(VarSym("person", Unknown), Unknown) :: Nil,
                                        Unknown) ::
                               BodyAtom(PredSym("Famous", Unknown),
                                        Positive,
                                        BodyVar(VarSym("person", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                               Unknown);
        fact1 :: fact2 :: fact3 :: fact4 :: rule1 :: Nil

    pub def bar() : List[Constraint[String]] =
        /// Edge(A, B).
        /// Edge(B, C).
        /// Edge(C, D).
        /// Vertex(x) :- Edge(x, _).
        /// Vertex(y) :- Edge(_, y).
        /// Path(x, y) :- Edge(x, y).
        /// Path(x, z) :- Path(x, y), Edge(y, z).
        /// Unconnected(x, y) :- Vertex(x), Vertex(y), not Path(x, y).
        /// AntiSymmetric(x, y) :- Path(x, y), not Path(y, x).
        let fact1 = Constraint(Nil, HeadAtom(PredSym("Edge", Unknown),
                                             HeadTerm.Lit("A", Unknown) ::
                                             HeadTerm.Lit("B", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let fact2 = Constraint(Nil, HeadAtom(PredSym("Edge", Unknown),
                                             HeadTerm.Lit("B", Unknown) ::
                                             HeadTerm.Lit("C", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let fact3 = Constraint(Nil, HeadAtom(PredSym("Edge", Unknown),
                                             HeadTerm.Lit("C", Unknown) ::
                                             HeadTerm.Lit("D", Unknown) :: Nil, Unknown),
                                Nil, Unknown);
        let rule1 = Constraint(VarSym("x", Unknown) :: VarSym("_", Unknown) :: Nil,
                                HeadAtom(PredSym("Vertex", Unknown),
                                         HeadTerm.Var(VarSym("x", Unknown), Unknown) :: Nil,
                                         Unknown),
                                BodyAtom(PredSym("Edge", Unknown),
                                        Positive,
                                        BodyVar(VarSym("x", Unknown), Unknown) ::
                                        BodyVar(VarSym("_", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                                Unknown);
        let rule2 = Constraint(VarSym("y", Unknown) :: VarSym("_", Unknown) :: Nil,
                                HeadAtom(PredSym("Vertex", Unknown),
                                        HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown),
                                BodyAtom(PredSym("Edge", Unknown),
                                        Positive,
                                        BodyVar(VarSym("_", Unknown), Unknown) ::
                                        BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                                Unknown);
        let rule3 = Constraint(VarSym("x", Unknown) :: VarSym("y", Unknown) :: Nil,
                                HeadAtom(PredSym("Path", Unknown),
                                        HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                        HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown),
                                BodyAtom(PredSym("Edge", Unknown),
                                        Positive,
                                        BodyVar(VarSym("x", Unknown), Unknown) ::
                                        BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                                Unknown);
        let rule4 = Constraint(VarSym("x", Unknown) :: VarSym("y", Unknown) :: VarSym("z", Unknown) :: Nil,
                                HeadAtom(PredSym("Path", Unknown),
                                        HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                        HeadTerm.Var(VarSym("z", Unknown), Unknown) :: Nil,
                                        Unknown),
                                BodyAtom(PredSym("Path", Unknown),
                                        Positive,
                                        BodyVar(VarSym("x", Unknown), Unknown) ::
                                        BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown) ::
                                BodyAtom(PredSym("Edge", Unknown),
                                        Positive,
                                        BodyVar(VarSym("y", Unknown), Unknown) ::
                                        BodyVar(VarSym("z", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                                Unknown);
        let rule5 = Constraint(VarSym("x", Unknown) :: VarSym("y", Unknown) :: Nil,
                                HeadAtom(PredSym("Unconnected", Unknown),
                                        HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                        HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown),
                                BodyAtom(PredSym("Vertex", Unknown),
                                        Positive,
                                        BodyVar(VarSym("x", Unknown), Unknown) :: Nil,
                                        Unknown) ::
                                BodyAtom(PredSym("Vertex", Unknown),
                                        Positive,
                                        BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown) ::
                                BodyAtom(PredSym("Path", Unknown),
                                        Negative,
                                        BodyVar(VarSym("x", Unknown), Unknown) ::
                                        BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                                Unknown);
        let rule6 = Constraint(VarSym("x", Unknown) :: VarSym("y", Unknown) :: Nil,
                                HeadAtom(PredSym("AntiSymmetric", Unknown),
                                        HeadTerm.Var(VarSym("x", Unknown), Unknown) ::
                                        HeadTerm.Var(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown),
                                BodyAtom(PredSym("Path", Unknown),
                                        Positive,
                                        BodyVar(VarSym("x", Unknown), Unknown) ::
                                        BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                        Unknown) ::
                                BodyAtom(PredSym("Path", Unknown),
                                        Negative,
                                        BodyVar(VarSym("y", Unknown), Unknown) ::
                                        BodyVar(VarSym("x", Unknown), Unknown) :: Nil,
                                        Unknown) :: Nil,
                                Unknown);
        fact1 :: fact2 :: fact3 :: rule1 :: rule2 :: rule3 :: rule4 :: rule5 :: rule6 :: Nil
}

namespace Fixpoint/Ram {
    pub enum Stmt[v] {
        case Insert(RelOp[v])
        case Merge(RelSym, RelSym)
        case Swap(RelSym, RelSym)
        case Purge(RelSym)
        case Seq(List[Stmt[v]])
        case While(BoolExp[v], Stmt[v])
    }

    pub enum RelOp[v] {
        case Search(RelSym, Option[BoolExp[v]], RelOp[v])
        case Project(List[RamTerm[v]], RelSym)
    }

    pub enum RelSym {
        case Full(String)
        case Delta(String)
        case New(String)
    }

    pub enum BoolExp[v] {
        case Empty(RelSym)
        case MemberOf(List[RamTerm[v]], RelSym)
        case Eq(RamTerm[v], RamTerm[v])
        case Not(BoolExp[v])
        case And(BoolExp[v], BoolExp[v])
    }

    pub enum RamTerm[v] {
        case Lit(v)
        case Attribute(Int32, Int32)
    }

    instance Monoid[Stmt[v]] {
        def empty(): Stmt[v] = Stmt.Seq(Nil)

        def combine(x: Stmt[v], y: Stmt[v]): Stmt[v] = match (x, y) {
            case (Stmt.Seq(xs), Stmt.Seq(ys)) => Stmt.Seq(xs ::: ys)
            case (x, Stmt.Seq(ys)) => Stmt.Seq(x :: ys)
            case (Stmt.Seq(xs), y) => Stmt.Seq(xs ::: y :: Nil)
            case _ => Stmt.Seq(x :: y :: Nil)
        }
    }

    instance Order[RelSym] {
        def less(a: RelSym, b: RelSym): Bool = match a <=> b {
            case LessThan => true
            case _ => false
        }

        def lessEqual(a: RelSym, b: RelSym): Bool = match a <=> b {
            case LessThan => true
            case EqualTo => true
            case _ => false
        }

        def greater(a: RelSym, b: RelSym): Bool = match a <=> b {
            case GreaterThan => true
            case _ => false
        }

        def greaterEqual(a: RelSym, b: RelSym): Bool = match a <=> b {
            case GreaterThan => true
            case EqualTo => true
            case _ => false
        }

        def compare(a: RelSym, b: RelSym): Comparison = match (a,b) {
            case (Full(s1), Full(s2))   => s1 <=> s2
            case (Delta(s1), Delta(s2)) => s1 <=> s2
            case (New(s1), New(s2))     => s1 <=> s2
            case (Full(_), _) => GreaterThan
            case (_, Full(_)) => LessThan
            case (Delta(_), New(_)) => GreaterThan
            case (New(_), Delta(_)) => LessThan
        }
    }
}
