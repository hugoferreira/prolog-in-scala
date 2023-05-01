sealed trait Term {
  val arity = 1
}

case class Atom(name: String) extends Term
case class Variable(name: String) extends Term
case class Compound(functor: String, arguments: Term*) extends Term {
  override val arity = arguments.length
}

case class Fact(functor: String, arguments: Term*) {
  val arity = arguments.length
}

// TODO Change Rule to have a head and a body, since the head is a mandatory part of a rule
case class Rule(head: Compound, body: Compound*) {
  val arity = body.length
}

def unify(term1: Term, term2: Term): Option[Map[String, Term]] = (term1, term2) match {
  case (Atom(name1), Atom(name2)) if name1 == name2 => Some(Map.empty[String, Term])
  case (Variable(name1), Variable(name2)) if name1 == name2 => Some(Map.empty[String, Term])
  case (v: Variable, _) => Some(Map(v.name -> term2))
  case (_, v: Variable) => Some(Map(v.name -> term1))
  case (Compound(functor1, args1*), Compound(functor2, args2*))
  if functor1 == functor2 && term1.arity == term2.arity =>
      unifyArgs(args1, args2, Map.empty[String, Term])
  case _ => None
}

def unifyArgs(args1: Seq[Term], args2: Seq[Term], substitution: Map[String, Term]): Option[Map[String, Term]] = {
  (args1, args2) match {
    case (Nil, Nil) => Some(substitution)
    case (arg1 +: rest1, arg2 +: rest2) =>
      unify(arg1, arg2) match {
        case Some(subst) =>
          val newSubstitution = substitution ++ subst
          unifyArgs(rest1, rest2, newSubstitution)
        case None => None
      }
    case _ => None
  }
}

def applySubstitution(term: Term, substitution: Map[String, Term]): Term = term match {
  case atom: Atom => atom
  case variable: Variable => substitution.getOrElse(variable.name, variable)
  case compound: Compound => 
    Compound(compound.functor, compound.arguments.map(arg => applySubstitution(arg, substitution)): _*)
}

unify(Atom("a"), Atom("a")) == Some(Map.empty)
unify(Atom("a"), Atom("b")) == None
unify(Variable("X"), Atom("a")) == Some(Map("X" -> Atom("a")))
unify(Atom("a"), Variable("X")) == Some(Map("X" -> Atom("a")))
unify(Variable("X"), Variable("X")) == Some(Map.empty)
unify(Compound("parent", Variable("X"), Compound("child", Atom("Alice"))),
      Compound("parent", Atom("john"), Compound("child", Atom("Alice"))))
      == Some(Map("X" -> Atom("john")))
unify(Compound("parent", Variable("X"), Variable("Y")),
      Compound("parent", Atom("john"), Compound("child", Atom("Alice"))))
      == Some(Map("X" -> Atom("john"), "Y" -> Compound("child", Atom("Alice"))))

applySubstitution(Atom("a"), Map.empty) == Atom("a")
applySubstitution(Variable("X"), Map.empty) == Variable("X")
applySubstitution(Variable("X"), Map("X" -> Atom("a"))) == Atom("a")
applySubstitution(Variable("X"), Map("Y" -> Atom("a"))) == Variable("X")
applySubstitution(Compound("f", Atom("a"), Atom("b")), Map.empty) == Compound("f", Atom("a"), Atom("b"))
applySubstitution(Compound("f", Variable("X"), Atom("b"), Variable("Y")), 
                  Map("X" -> Atom("a"), "Y" -> Atom("c"))) 
                  == Compound("f", Atom("a"), Atom("b"), Atom("c"))
applySubstitution(Compound("f", Variable("X"), Compound("g", Variable("Y"), Atom("b"))), 
                  Map("X" -> Atom("a"), "Y" -> Atom("c"))) 
                  == Compound("f", Atom("a"), Compound("g", Atom("c"), Atom("b")))
applySubstitution(Compound("parent", Variable("X"), Variable("Y")), 
                  Map("X" -> Atom("john"), "Y" -> Compound("child", Atom("Alice")))) 
                  == Compound("parent", Atom("john"), Compound("child", Atom("Alice")))


// def search(goals: List[Compound], facts: List[Fact], rules: List[Rule], substitution: Map[String, Term]): LazyList[Map[String, Term]] = {
//   if (goals.isEmpty) return LazyList(substitution)

//   val (selectedGoal, remainingGoals) = (goals.head, goals.tail)

//   facts.to(LazyList)
//        .flatMap { fact => unify(selectedGoal, Compound(fact.functor, fact.arguments: _*)) }
//        .flatMap { unificationResult =>
//           val newSubstitution = substitution ++ unificationResult
//           val newGoals = applySubstitutionToGoals(remainingGoals, newSubstitution)
//           search(newGoals, facts, rules, newSubstitution) 
//         }
// }

given Conversion[Fact, Compound] = fact => Compound(fact.functor, fact.arguments: _*)

def search(goals: List[Compound], facts: List[Fact], rules: List[Rule], substitution: Map[String, Term]): LazyList[Map[String, Term]] = {
  if (goals.isEmpty) return LazyList(substitution)

  val (selectedGoal, remainingGoals) = (goals.head, goals.tail)

  // Unify with facts
  val factUnifications = facts.to(LazyList).flatMap { fact => unify(selectedGoal, fact) }

  // Unify with rule heads
  val ruleUnifications = rules.to(LazyList)
    .flatMap { rule =>
      unify(selectedGoal, rule.head).map { unificationResult =>
        (rule, unificationResult)
      }
    }

  // Combine fact and rule unifications
  val combinedUnifications = factUnifications.map((None, _)) ++ ruleUnifications.map(ru => (Some(ru._1), ru._2))

  combinedUnifications.flatMap { case (maybeRule, unificationResult) =>
    val newSubstitution = substitution ++ unificationResult

    // Apply the substitution to the remaining goals
    val newGoals = applySubstitutionToGoals(remainingGoals, newSubstitution)

    // If a unifying rule was found, add its body goals to the new goals list
    maybeRule match {
      case Some(rule) =>
        val ruleBodyGoals = rule.body.toList.map(compound => applySubstitutionToCompound(compound, unificationResult).asInstanceOf[Compound])
        search(newGoals ++ ruleBodyGoals, facts, rules, newSubstitution)
      case None =>
        search(newGoals, facts, rules, newSubstitution)
    }
  }
}

def applySubstitutionToCompound(compound: Compound, substitution: Map[String, Term]): Compound = {
  Compound(compound.functor, compound.arguments.map(arg => applySubstitution(arg, substitution)): _*)
}

def applySubstitutionToGoals(goals: List[Compound], substitution: Map[String, Term]): List[Compound] = {
  goals.map { compound => applySubstitutionToCompound(compound, substitution) }
}

val rules = List(
  Rule(
    Compound("grandparent", Variable("X"), Variable("Z")),
    Compound("parent", Variable("X"), Variable("Y")),
    Compound("parent", Variable("Y"), Variable("Z"))
  )
)
val facts = List(
  Fact("parent", Atom("john"), Atom("alice")),
  Fact("parent", Atom("john"), Atom("bob")),
  Fact("parent", Atom("jane"), Atom("alice")),
  Fact("parent", Atom("jane"), Atom("bob")),
  Fact("parent", Atom("bob"), Atom("carol")),
  Fact("parent", Atom("bob"), Atom("david"))
)

search(List(Compound("parent", Variable("G"), Atom("alice"))), facts, rules, Map.empty).drop(1).head
search(List(Compound("grandparent", Variable("G"), Atom("carol"))), facts, rules, Map.empty).drop(1).head

// == LazyList(Map("G" -> Atom("john")), Map("G" -> Atom("jane")))

