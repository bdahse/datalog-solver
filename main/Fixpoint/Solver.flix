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
            let rule1 = Constraint(ConstraintParam(VarSym("person", Unknown), Unknown) :: Nil,
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
                                                 HeadLit("A", Unknown) ::
                                                 HeadLit("B", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact2 = Constraint(Nil, HeadAtom(PredSym("Edge", Unknown),
                                                 HeadLit("B", Unknown) ::
                                                 HeadLit("C", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let fact3 = Constraint(Nil, HeadAtom(PredSym("Edge", Unknown),
                                                 HeadLit("C", Unknown) ::
                                                 HeadLit("D", Unknown) :: Nil, Unknown),
                                   Nil, Unknown);
            let rule1 = Constraint(ConstraintParam(VarSym("x", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("_", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Vertex", Unknown),
                                            HeadVar(VarSym("x", Unknown), Unknown) :: Nil,
                                            Unknown),
                                   BodyAtom(PredSym("Edge", Unknown),
                                            Positive,
                                            BodyVar(VarSym("x", Unknown), Unknown) ::
                                            BodyVar(VarSym("_", Unknown), Unknown) :: Nil,
                                            Unknown) :: Nil,
                                   Unknown);
            let rule2 = Constraint(ConstraintParam(VarSym("y", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("_", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Vertex", Unknown),
                                            HeadVar(VarSym("y", Unknown), Unknown) :: Nil,
                                            Unknown),
                                   BodyAtom(PredSym("Edge", Unknown),
                                            Positive,
                                            BodyVar(VarSym("_", Unknown), Unknown) ::
                                            BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                            Unknown) :: Nil,
                                   Unknown);
            let rule3 = Constraint(ConstraintParam(VarSym("x", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("y", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Path", Unknown),
                                            HeadVar(VarSym("x", Unknown), Unknown) ::
                                            HeadVar(VarSym("y", Unknown), Unknown) :: Nil,
                                            Unknown),
                                   BodyAtom(PredSym("Edge", Unknown),
                                            Positive,
                                            BodyVar(VarSym("x", Unknown), Unknown) ::
                                            BodyVar(VarSym("y", Unknown), Unknown) :: Nil,
                                            Unknown) :: Nil,
                                   Unknown);
            let rule4 = Constraint(ConstraintParam(VarSym("x", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("y", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("z", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Path", Unknown),
                                            HeadVar(VarSym("x", Unknown), Unknown) ::
                                            HeadVar(VarSym("z", Unknown), Unknown) :: Nil,
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
            let rule5 = Constraint(ConstraintParam(VarSym("x", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("y", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("Unconnected", Unknown),
                                            HeadVar(VarSym("x", Unknown), Unknown) ::
                                            HeadVar(VarSym("y", Unknown), Unknown) :: Nil,
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
            let rule6 = Constraint(ConstraintParam(VarSym("x", Unknown), Unknown) ::
                                   ConstraintParam(VarSym("y", Unknown), Unknown) :: Nil,
                                   HeadAtom(PredSym("AntiSymmetric", Unknown),
                                            HeadVar(VarSym("x", Unknown), Unknown) ::
                                            HeadVar(VarSym("y", Unknown), Unknown) :: Nil,
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

    namespace RelationalAlgebraMachine {

        // TODO

    }

}
