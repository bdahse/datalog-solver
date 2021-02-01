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

        pub enum Constraint {
            case Constraint(List[ConstraintParam], HeadPredicate, List[BodyPredicate])
        }

        pub enum ConstraintParam {
            // TODO
            case ConstraintParam(VarSym)
        }

        pub enum HeadPredicate {
            // TODO
            case Atom(PredSym, List[HeadTerm])
        }

        pub enum PredSym {
            case PredSym(String)
        }

        pub enum HeadTerm {
            case QuantVar(VarSym),
            case Lit(String)
        }

        pub enum VarSym {
            case VarSym(String)
        }

        pub enum BodyPredicate {
            case Atom(PredSym, List[BodyTerm])
        }

        pub enum BodyTerm {
            case QuantVar(VarSym),
            case Lit(String)
        }

        pub enum SourceLocation {
            // TODO
        }

        pub def foo() : List[Constraint] =
            let fact1 = Constraint(Nil, HeadPredicate.Atom(PredSym("Rich"), HeadTerm.Lit("Magnus") :: Nil), Nil);
            let fact2 = Constraint(Nil, HeadPredicate.Atom(PredSym("Age"), HeadTerm.Lit("34") :: Nil), Nil);
            let fact3 = Constraint(Nil, HeadPredicate.Atom(PredSym("Rich"), HeadTerm.Lit("Joakim") :: Nil), Nil);
            let fact4 = Constraint(Nil, HeadPredicate.Atom(PredSym("Famous"), HeadTerm.Lit("Joakim") :: Nil), Nil);
            let rule1 = Constraint(ConstraintParam(VarSym("person")) :: Nil,
                                    HeadPredicate.Atom(PredSym("Happy"),
                                        HeadTerm.QuantVar(VarSym("person")) :: Nil),
                                    BodyPredicate.Atom(PredSym("Rich"), BodyTerm.QuantVar(VarSym("person")) :: Nil) ::
                                    BodyPredicate.Atom(PredSym("Famous"), BodyTerm.QuantVar(VarSym("person")) :: Nil) :: Nil);
            fact1 :: fact2 :: fact3 :: fact4 :: rule1 :: Nil
    }

    namespace RelationalAlgebraMachine {

        // TODO

    }

}
/// Rich("Magnus").
/// Age(34).
/// Rich("Joakim").
/// Famous("Joakim").
/// Happy(person) :- Rich(person), Famous(person).