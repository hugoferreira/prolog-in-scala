sealed trait Term {
  val arity = 1
}

case class Atom(name: String) extends Term
case class Variable(name: String, var clause: Option[Clause] = None) extends Term {
  override def toString(): String = s"Variable($name, ${clause.map(_.name).getOrElse("None")})"
}

case class Compound(functor: String, arguments: Term*) extends Term {
  override val arity = arguments.length
}

case class Clause(head: Compound, body: List[Compound]) {
  val arity = body.length
  val name = head.functor
}

object Clause {
  def rewriteVariableClause(compound: Compound, clause: Clause): Unit = {
    compound.arguments.foreach {
      case v: Variable => v.clause = Some(clause)
      case _ => ()
    }
  }
  
  def fact(functor: String, arguments: Term*): Clause = {
    Clause(Compound(functor, arguments: _*), List.empty)
  }

  def rule(head: Compound, body: Compound*): Clause = {
    val clause = Clause(head, body.toList)
    rewriteVariableClause(head, clause)
    body.foreach { c => rewriteVariableClause(c, clause) }
    clause
  }

  def compound(functor: String, arguments: String*): Compound = {
    Compound(functor, arguments.map(_ match {
      case s if s.head.isUpper => Variable(s)
      case s => Atom(s)
    }): _*)
  }
}

object BuiltInPredicates {
  def not_equal(using substitution: Map[Variable, Term])(arg1: Term, arg2: Term): Option[Map[Variable, Term]] = {
    InferenceEngine.applySubstitution(arg1) != InferenceEngine.applySubstitution(arg2) match {
      case true => Some(substitution)
      case false => None
    }
  }
}

object InferenceEngine {
  def unify(term1: Term, term2: Term): Option[Map[Variable, Term]] = (term1, term2) match {
    case (Atom(name1), Atom(name2)) if name1 == name2 => Some(Map.empty)
    case (Variable(name1, clause1), Variable(name2, clause2)) if name1 == name2 && clause1 == clause2 => Some(Map.empty)
    case (v: Variable, _) => Some(Map(v -> term2))
    case (_, v: Variable) => Some(Map(v -> term1))
    case (Compound(functor1, args1*), Compound(functor2, args2*))
      if functor1 == functor2 && term1.arity == term2.arity =>
        unifyArgs(args1, args2, Map.empty)
    case _ => None
  }

  def unifyArgs(args1: Seq[Term], args2: Seq[Term], substitution: Map[Variable, Term]): Option[Map[Variable, Term]] = {
    (args1, args2) match {
      case (Nil, Nil) => Some(substitution)
      case (arg1 +: rest1, arg2 +: rest2) =>
        unify(arg1, arg2) match {
          case Some(subst) =>
            unifyArgs(rest1, rest2, substitution ++ subst)
          case None => None
        }
      case _ => None
    }
  }

  def applySubstitution(using substitution: Map[Variable, Term])(term: Term): Term = term match {
    case atom: Atom => atom
    case variable: Variable => substitution.getOrElse(variable, variable)
    case Compound(functor, arguments*) => 
      Compound(functor, arguments.map(arg => applySubstitution(arg)): _*)
  }

  def search(using substitution: Map[Variable, Term])(goals: List[Compound], clauses: List[Clause]): LazyList[Map[Variable, Term]] = {
    if (goals.isEmpty) return LazyList(substitution)

    val (selectedGoal, remainingGoals) = (goals.head, goals.tail)

    selectedGoal.functor match {
      case "not_equal" => // Special functor handling
        BuiltInPredicates.not_equal(selectedGoal.arguments(0), selectedGoal.arguments(1)) match {
          case Some(newSubstitution) => search(using newSubstitution)(remainingGoals, clauses)
          case None => LazyList.empty
        }

      case _ => // Regular case, unchanged from before
        for {
          clause <- clauses.to(LazyList)
          unificationResult <- unify(selectedGoal, clause.head).to(LazyList)
          newSubstitution = substitution ++ unificationResult
          newGoals = applySubstitutionToCompounds(using newSubstitution)(remainingGoals)
          result <- search(
            newGoals ++ (if (clause.body.nonEmpty) applySubstitutionToCompounds(using unificationResult)(clause.body) else List.empty),
            clauses
          )
        } yield result
    }
  }

  def applySubstitutionToCompounds(using substitution: Map[Variable, Term])(compounds: List[Compound]): List[Compound] = {
    compounds.map { compound => 
      Compound(compound.functor, compound.arguments.map(arg => applySubstitution(arg)): _*) }
  }

  def chase(variable: Variable, substitution: Map[Variable, Term]): Term = {
    substitution.get(variable) match {
      case Some(v: Variable) => chase(v, substitution)
      case Some(term) => term
      case None => variable
    }
  }

  def query(using substitution: Map[Variable, Term] = Map())(goal: Compound, clauses: List[Clause]): LazyList[Map[Variable, Term]] = {
    val goals = List(goal)
    val searchResults = search(goals, clauses)

    searchResults.map { resultSubstitution =>
      goal.arguments.collect {
        case v: Variable => v -> chase(v, resultSubstitution)
      }.toMap
    }
  }
}

import InferenceEngine._

unify(Atom("a"), Atom("a")) == Some(Map.empty)
unify(Atom("a"), Atom("b")) == None
unify(Variable("X"), Atom("a")) == Some(Map(Variable("X") -> Atom("a")))
unify(Atom("a"), Variable("X")) == Some(Map(Variable("X") -> Atom("a")))
unify(Variable("X"), Variable("X")) == Some(Map.empty)
unify(Compound("parent", Variable("X"), Compound("child", Atom("Alice"))),
      Compound("parent", Atom("john"), Compound("child", Atom("Alice"))))
      == Some(Map(Variable("X") -> Atom("john")))
unify(Compound("parent", Variable("X"), Variable("Y")),
      Compound("parent", Atom("john"), Compound("child", Atom("Alice"))))
      == Some(Map(Variable("X") -> Atom("john"), Variable("Y") -> Compound("child", Atom("Alice"))))

applySubstitution(using Map.empty)(Atom("a")) == Atom("a")
applySubstitution(using Map.empty)(Variable("X")) == Variable("X")
applySubstitution(using Map(Variable("X") -> Atom("a")))(Variable("X")) == Atom("a")
applySubstitution(using Map(Variable("Y") -> Atom("a")))(Variable("X")) == Variable("X")
applySubstitution(using Map.empty)(Compound("f", Atom("a"), Atom("b"))) == Compound("f", Atom("a"), Atom("b"))
applySubstitution(using Map(Variable("X") -> Atom("a"), Variable("Y") -> Atom("c")))
                 (Compound("f", Variable("X"), Atom("b"), Variable("Y")))   
                  == Compound("f", Atom("a"), Atom("b"), Atom("c"))
applySubstitution(using Map(Variable("X") -> Atom("a"), Variable("Y") -> Atom("c")))
                 (Compound("f", Variable("X"), Compound("g", Variable("Y"), Atom("b"))))                    
                  == Compound("f", Atom("a"), Compound("g", Atom("c"), Atom("b")))
applySubstitution(using Map(Variable("X") -> Atom("john"), Variable("Y") -> Compound("child", Atom("Alice"))))
                 (Compound("parent", Variable("X"), Variable("Y")))                  
                  == Compound("parent", Atom("john"), Compound("child", Atom("Alice")))

val program = List(
  Clause.fact("parent", Atom("john"), Atom("alice")),
  Clause.fact("parent", Atom("jane"), Atom("alice")),
  Clause.fact("parent", Atom("jane"), Atom("bob")),
  Clause.fact("parent", Atom("john"), Atom("bob")),
  Clause.fact("parent", Atom("bob"), Atom("carol")),
  Clause.fact("parent", Atom("bob"), Atom("david")),
  Clause.rule(
    Clause.compound("grandparent", "X", "Z"),
    Clause.compound("parent", "X", "Y"),
    Clause.compound("parent", "Y", "Z")
  ),
  Clause.rule(
    Clause.compound("sibling", "X", "Y"),
    Clause.compound("parent", "Z", "X"),
    Clause.compound("parent", "Z", "Y"),
    Clause.compound("not_equal", "X", "Y")
  )
)

query(Clause.compound("parent", "G", "alice"), program).toList
query(Clause.compound("grandparent", "G", "carol"), program).toList

query(Clause.compound("sibling", "bob", "Y"), program).toList