/*
 * Copyright 2021 Magnus Madsen
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

namespace Fixpoint {

    namespace Ast {

        pub enum Constraint[v] {
            case Constraint(List[ConstraintParam], HeadPredicate[v], List[BodyPredicate[v]], SourceLocation)
        }

        pub enum ConstraintParam {
            case HeadParam(VarSym, SourceLocation),
            case RuleParam(VarSym, SourceLocation)
        }

        pub enum HeadPredicate[v] {
            case HeadAtom(PredSym, List[HeadTerm[v]], SourceLocation)
        }

        pub enum BodyPredicate[v] {
            case BodyAtom(PredSym, Polarity, List[BodyTerm[v]], SourceLocation)
        }

        pub enum HeadTerm[v] {
            case HeadVar(VarSym, SourceLocation)
            case HeadLit(v, SourceLocation)
        }

        pub enum BodyTerm[v] {
            case BodyVar(VarSym, SourceLocation)
            case BodyLit(v, SourceLocation)
        }

        pub enum Polarity {
            case Positive,
            case Negative
        }

        pub enum PredSym {
            case PredSym(String, SourceLocation)
        }

        pub enum VarSym {
            case VarSym(String, SourceLocation)
        }

        pub enum SourceLocation {
            case Unknown,
            case SourceLocation({name: String, beginLine: Int32, beginCol: Int32, endLine: Int32, endCol: Int32})
        }

        pub opaque type PrecedenceGraph[v] = Set[PrecedenceEdge[v]]

        pub enum PrecedenceEdge[v] {
            case PositiveEdge(BodyPredicate[v], HeadPredicate[v]),
            case NegativeEdge(BodyPredicate[v], HeadPredicate[v])
        }

        pub def precedence(cs: List[Constraint[v]]): PrecedenceGraph[v] =
            List.foldLeft((acc, c) -> match c {
                case Constraint(_, head, body, _) => precedenceHelper(acc, head, body)
            }, PrecedenceGraph(Set#{}), cs)

        def precedenceHelper[v](g: PrecedenceGraph[v], head: HeadPredicate[v], body: List[BodyPredicate[v]]): PrecedenceGraph[v] =
            List.foldLeft((acc, bp) -> match (acc, bp) {
                case (PrecedenceGraph(edges), BodyAtom(_, Positive, _, _)) =>
                    PrecedenceGraph(Set.union(edges, Set#{PositiveEdge(bp, head)}))
                case (PrecedenceGraph(edges), BodyAtom(_, Negative, _, _)) =>
                    PrecedenceGraph(Set.union(edges, Set#{NegativeEdge(bp, head)}))
            }, g, body)

        pub def isRangeRestricted(p: List[Constraint[v]]): Bool =
            List.forall(rangeRestrictedHelper, p)

        def rangeRestrictedHelper(c: Constraint[v]): Bool = match c {
            case Constraint(params, _, _, _) => headVars(params) `Set.isSubsetOf` ruleVars(params)
        }

        def headVars(params: List[ConstraintParam]): Set[VarSym] =
            List.foldLeft((acc, p) -> match p {
                case HeadParam(var, _) => Set.union(acc, Set#{var})
                case _ => acc
            }, Set#{}, params)

        def ruleVars(params: List[ConstraintParam]): Set[VarSym] =
            List.foldLeft((acc, p) -> match p {
                case RuleParam(var, _) => Set.union(acc, Set#{var})
                case _ => acc
            }, Set#{}, params)

        pub def nonPositivelyBoundVar(cs: List[Constraint[v]]): Bool =
            List.forall(c -> match c {
                case Constraint(_, _, body, _) =>
                    let (positive, negative) = polarityVars(body);
                    negative `Set.isSubsetOf` positive
            }, cs)

        def polarityVars(body: List[BodyPredicate[v]]): (Set[VarSym], Set[VarSym]) =
            List.foldLeft((acc, bp) -> match (acc, bp) {
                case ((p, n), BodyAtom(_, Positive, terms, _)) => (Set.union(p, termVars(terms)), n)
                case ((p, n), BodyAtom(_, Negative, terms, _)) => (p, Set.union(n, termVars(terms)))
            }, (Set#{}, Set#{}), body)

        def termVars[v](terms: List[BodyTerm[v]]): Set[VarSym] =
            List.foldLeft((acc, t) -> match t {
                case BodyVar(var, _) => Set.union(acc, Set#{var})
                case _ => acc
            }, Set#{}, terms)

        instance Order[VarSym] {
            def less(a: VarSym, b: VarSym): Bool = match a <=> b {
                case LessThan => true
                case _ => false
            }

            def lessEqual(a: VarSym, b: VarSym): Bool = match a <=> b {
                case LessThan => true
                case EqualTo => true
                case _ => false
            }

            def greater(a: VarSym, b: VarSym): Bool = match a <=> b {
                case GreaterThan => true
                case _ => false
            }

            def greaterEqual(a: VarSym, b: VarSym): Bool = match a <=> b {
                case GreaterThan => true
                case EqualTo => true
                case _ => false
            }

            def compare(a: VarSym, b: VarSym): Comparison = match (a,b) {
                case (VarSym(s1, _), VarSym(s2, _)) => s1 <=> s2
            }
        }

        instance Order[PredSym] {

            def less(a: PredSym, b: PredSym): Bool = match a <=> b {
                case LessThan => true
                case _ => false
            }

            def lessEqual(a: PredSym, b: PredSym): Bool = match a <=> b {
                case LessThan => true
                case EqualTo => true
                case _ => false
            }

            def greater(a: PredSym, b: PredSym): Bool = match a <=> b {
                case GreaterThan => true
                case _ => false
            }

            def greaterEqual(a: PredSym, b: PredSym): Bool = match a <=> b {
                case GreaterThan => true
                case EqualTo => true
                case _ => false
            }

            def compare(a: PredSym, b: PredSym): Comparison = match (a,b) {
                case (PredSym(s1, _), PredSym(s2, _)) => s1 <=> s2
            }

        }

        instance Order[PrecedenceEdge[a]] {

            def less(a: PrecedenceEdge[v], b: PrecedenceEdge[v]): Bool = match a <=> b {
                case LessThan => true
                case _ => false
            }

            def lessEqual(a: PrecedenceEdge[v], b: PrecedenceEdge[v]): Bool = match a <=> b {
                case LessThan => true
                case EqualTo => true
                case _ => false
            }

            def greater(a: PrecedenceEdge[v], b: PrecedenceEdge[v]): Bool = match a <=> b {
                case GreaterThan => true
                case _ => false
            }

            def greaterEqual(a: PrecedenceEdge[v], b: PrecedenceEdge[v]): Bool = match a <=> b {
                case GreaterThan => true
                case EqualTo => true
                case _ => false
            }

            def compare(a: PrecedenceEdge[v], b: PrecedenceEdge[v]): Comparison = match (a,b) {
                case (PositiveEdge(BodyAtom(s1, _, _, _), HeadAtom(s2, _, _)),
                      PositiveEdge(BodyAtom(s3, _, _, _), HeadAtom(s4, _, _))) =>
                      let cmp = s1 <=> s3;
                      if (cmp == EqualTo)
                        s2 <=> s4
                      else
                        cmp
                case (NegativeEdge(BodyAtom(s1, _, _, _), HeadAtom(s2, _, _)),
                      NegativeEdge(BodyAtom(s3, _, _, _), HeadAtom(s4, _, _))) =>
                      let cmp = s1 <=> s3;
                      if (cmp == EqualTo)
                        s2 <=> s4
                      else
                        cmp
                case (NegativeEdge(_, _), PositiveEdge(_, _)) => LessThan
                case (PositiveEdge(_, _), NegativeEdge(_, _)) => GreaterThan
            }

        }

        pub def foo() : List[Constraint[String]] =
            /// Rich("Magnus").
            /// Age(34).
            /// Rich("Joakim").
            /// Famous("Joakim").
            /// Happy(person) :- Rich(person), Famous(person).
            // TODO: Find out how to make this a testcase.
            let fact1 = Constraint(Nil, HeadAtom(PredSym("Rich", Unknown),
                                                 HeadLit("Magnus", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact2 = Constraint(Nil, HeadAtom(PredSym("Age", Unknown),
                                                 HeadLit("34", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact3 = Constraint(Nil, HeadAtom(PredSym("Rich", Unknown),
                                                 HeadLit("Joakim", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact4 = Constraint(Nil, HeadAtom(PredSym("Famous", Unknown),
                                                 HeadLit("Joakim", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let rule1 = Constraint(HeadParam(VarSym("person", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Happy", Unknown),
                                            HeadVar(VarSym("person", Unknown), Unknown) :: Nil,
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
    }

    namespace RelationalAlgebraMachine {

        // TODO

    }

}
