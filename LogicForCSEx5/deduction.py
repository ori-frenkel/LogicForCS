# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *

def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)
    # Task 5.3a
    statement = InferenceRule(antecedent_proof.statement.assumptions,
                                       consequent)

    all_lines = list()
    count = 0
    # coping all the antecedent_proof
    for line in antecedent_proof.lines:
        count +=1
        all_lines.append(line)
    # copying the right (p->q) using the conditional rule
    all_lines.append(Proof.Line(Formula('->', antecedent_proof.statement.conclusion,
                                        statement.conclusion),conditional, []))
    # using MP rule on the last two lines.
    all_lines.append(Proof.Line(statement.conclusion, MP,[count - 1, count]))

    all_rules = list()
    for rule in antecedent_proof.rules:
        all_rules.append(rule)
    all_rules.append(conditional)

    return Proof(statement, all_rules, all_lines)

def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
        Formula('->', antecedent2_proof.statement.conclusion, consequent))
        ).is_specialization_of(double_conditional)
    # Task 5.3b
    # consequent -> statement conclusion
    # proof1 = prove_corollary(antecedent1_proof, antecedent2_proof.statement.conclusion, double_conditional)
    # combined = prove_corollary(antecedent2_proof, consequent, double_conditional)

    # antecedent1_proof and antecedent2_proof has the same assumptions
    statement = InferenceRule(antecedent1_proof.statement.assumptions,
                                       consequent)

    all_rules = list()
    for rule in antecedent1_proof.rules:
        all_rules.append(rule)
    all_rules.append(double_conditional)

    all_lines = list()
    count = 0
    for line in antecedent1_proof.lines:
        count +=1
        all_lines.append(line)
    part1_idx = count
    for line in antecedent2_proof.lines:
        count+=1
        # because all of this proof come after antecedent1_proof, need to
        # shift all the assumptions idx by number of line in the antecedent1_proof
        shift_line_assumptions(all_lines, part1_idx, line)
    part2_idx = count
    # (part1->(part2->c)) = (a->(b->c))
    # part3 = (part2->c) = (part2->consequent)
    part3 = Formula('->',all_lines[part2_idx - 1].formula, consequent)
    all_lines.append(Proof.Line(Formula('->',all_lines[part1_idx - 1].formula,part3), double_conditional, []))
    count +=1

    # first MP
    all_lines.append(Proof.Line(part3, MP, [part1_idx - 1, count - 1]))
    count +=1
    # second MP (and than finished).
    all_lines.append(Proof.Line(consequent, MP, [part2_idx - 1, count - 1]))

    return Proof(statement, all_rules, all_lines)

# this function gets new_line_proof which hold the index of the new line
# meaning : new_lines_of_proof[1] -> will return the line number of p->a
#  where a is what what was in old proof
def convert_assumption_line(new_line_proof, old_proof_idx):
    to_return = list()
    for idx in old_proof_idx:
        to_return.append(new_line_proof[idx])
    return to_return

def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """        
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.4
    # count - represent the number of line that we added so far compare to the
    #         original proof.
    count = 0
    last_assumption = proof.statement.assumptions[-1]
    # the new set of assumption is : (same without last assumption)
    assumption_without_last = proof.statement.assumptions[:-1]
    new_statement = InferenceRule(assumption_without_last, Formula('->', last_assumption, proof.statement.conclusion))
    all_lines = list()
    # represent at the arr[1] = the index in the new proof where p->a
    # where a is old_proof[1] = a
    new_lines_of_proof = list()
    for idx,line in enumerate(proof.lines):
        # we want to prove that 'p->statement.conclusion' where p is the
        #  last assumption
        if line.formula == last_assumption:
            # if it is the assumption that we  removed from the
            # list of assumption (lest call it p)
            # we can write '(p->p)' and its valid from I0
            all_lines.append(Proof.Line(
                Formula('->', last_assumption, last_assumption),
                I0, []))
            new_lines_of_proof.append(idx + count)


        elif line in assumption_without_last or line.rule != MP:
            # I would mark the assumption by 'q'
            all_lines.append(line) # adding the assumption it self
                                   #  or the rule (without assumption)
            count +=1

            #(q->(p->q)), lets mark part2 = (p->q)
            part2 = Formula('->',last_assumption,line.formula)
            pqp = Formula('->', line.formula, part2)

            all_lines.append(Proof.Line(pqp, I1, []))

            # all_lines.append(Proof.Line(pqp, I1, []))
            count +=1

            # no need to shift, using the last two lines.
            all_lines.append(Proof.Line(part2, MP , [(len(all_lines) - 2), (len(all_lines) - 1)]))
            new_lines_of_proof.append(idx + count)


        else: # line rule is MP
            # ((p ->(a->b))->((p->a)->(p->b)))
            # part3 = ((p ->(a->b))
            # part4 = (p->a)
            # part5 = (p->b)


            part3 = all_lines[new_lines_of_proof[line.assumptions[1]]]

            part4 = all_lines[new_lines_of_proof[line.assumptions[0]]]

            part5 = Formula("->", last_assumption , line.formula)

            all_lines.append(Proof.Line(Formula('->', part3.formula,
                                                Formula('->',part4.formula,part5))
                                        , D, []))
            count +=1

            all_lines.append(Proof.Line(Formula('->',part4.formula,part5), MP,
                                        [new_lines_of_proof[line.assumptions[1]]
                                            , len(all_lines)-1]))
            count+=1

            all_lines.append(Proof.Line(part5, MP,
                                        [new_lines_of_proof[line.assumptions[0]],
                                         len(all_lines) - 1]))
            new_lines_of_proof.append(idx + count)


    # adding to the rules I0,I1,D,MP
    rule_to_append = [I0,I1,D,MP]
    new_rules = list()
    for rule in proof.rules:
        if rule in rule_to_append:
            continue
        new_rules.append(rule)
    for rule in rule_to_append:
        new_rules.append(rule)

    return Proof(new_statement, new_rules, all_lines)





def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules
    # Task 5.6

def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0
    # Task 5.7
