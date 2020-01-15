# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/proofs.py

"""Proofs by deduction in propositional logic."""

from __future__ import annotations
from typing import AbstractSet, Iterable, FrozenSet, List, Mapping, Optional, \
                   Set, Tuple, Union

from logic_utils import frozen

from propositions.syntax import *

SpecializationMap = Mapping[str, Formula]

@frozen
class InferenceRule:
    """An immutable inference rule in propositional logic, comprised by zero
    or more assumed propositional formulae, and a conclusion propositional
    formula.

    Attributes:
        assumptions (`~typing.Tuple`\\[`~propositions.syntax.Formula`, ...]):
            the assumptions of the rule.
        conclusion (`~propositions.syntax.Formula`): the conclusion of the rule.
    """
    assumptions: Tuple[Formula, ...]
    conclusion: Formula

    def __init__(self, assumptions: Iterable[Formula], conclusion: Formula) -> \
        None:
        """Initialized an `InferenceRule` from its assumptions and conclusion.

        Parameters:
            assumptions: the assumptions for the rule.
            conclusion: the conclusion for the rule.
        """
        self.assumptions = tuple(assumptions)
        self.conclusion = conclusion

    def __eq__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is an `InferenceRule` object that
            equals the current inference rule, ``False`` otherwise.
        """
        return (isinstance(other, InferenceRule) and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other: object) -> bool:
        """Compares the current inference rule with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not an `InferenceRule` object or
            does not does not equal the current inference rule, ``False``
            otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes a string representation of the current inference rule.

        Returns:
            A string representation of the current inference rule.
        """
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current inference
        rule.

        Returns:
            A set of all atomic propositions used in the assumptions and in the
            conclusion of the current inference rule.
        """
        # get variables from conclusion
        variables = Formula.variables(self.conclusion)
        # get variables from all assumptions and union them together
        for assumption in self.assumptions:
            variables = variables.union(Formula.variables(assumption))
        return variables
        # Task 4.1

    def specialize(self, specialization_map: SpecializationMap) -> \
            InferenceRule:
        """Specializes the current inference rule by simultaneously substituting
        each variable `v` that is a key in `specialization_map` with the
        formula `specialization_map[v]`.

        Parameters:
            specialization_map: mapping defining the specialization to be
                performed.

        Returns:
            The resulting inference rule.
        """
        for variable in specialization_map:
            assert is_variable(variable)

        # get specialized assumptions tuple
        assumptions = list()
        for assumption in self.assumptions:
            assumptions.append(Formula.substitute_variables(assumption, specialization_map))
        assumptions = tuple(assumptions)
        # get specialized conclusion
        conclusion = Formula.substitute_variables(self.conclusion, specialization_map)

        return InferenceRule(assumptions, conclusion)
        # Task 4.4

    @staticmethod
    def merge_specialization_maps(
            specialization_map1: Union[SpecializationMap, None],
            specialization_map2: Union[SpecializationMap, None]) -> \
            Union[SpecializationMap, None]:
        """Merges the given specialization maps.

        Parameters:
            specialization_map1: first map to merge, or ``None``.
            specialization_map2: second map to merge, or ``None``.

        Returns:
            A single map containing all (key, value) pairs that appear in
            either of the given maps, or ``None`` if one of the given maps is
            ``None`` or if some key appears in both given maps but with
            different values.
        """
        if specialization_map1 is not None:
            for variable in specialization_map1:
                assert is_variable(variable)
        if specialization_map2 is not None:
            for variable in specialization_map2:
                assert is_variable(variable)

        # check if the mappings are illegal
        if specialization_map1 is None or specialization_map2 is None:
            return None
        # check if one of the keys appear in both maps with different values
        for variable in specialization_map1:
            if variable in specialization_map2 and \
                    specialization_map1[variable] != specialization_map2[variable]:
                return None

        # else, legal mappings
        merged = dict()
        for variable in specialization_map1:
            merged[variable] = specialization_map1[variable]
        for variable in specialization_map2:
            merged[variable] = specialization_map2[variable]
        return merged
        # Task 4.5a

    @staticmethod
    def formula_specialization_map(general: Formula, specialization: Formula) \
            -> Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the given formula
        specializes to the given specialization.

        Parameters:
            general: non-specialized formula for which to compute the map.
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of `general`.
        """
        # general.root is a constant check if specialized root is same constant
        if is_constant(general.root) and is_constant(specialization.root):
            if general.root == specialization.root:
                return {}
            # else, the constants aren't equal
            return None

        # general.root is a variable
        if is_variable(general.root):
            return {general.root: specialization}

        # general.root is an unary operation
        if is_unary(general.root) and is_unary(specialization.root) and \
                general.root == specialization.root:
            return InferenceRule.formula_specialization_map(general.first, specialization.first)

        # general.root is a binary operation
        if is_binary(general.root) and is_binary(specialization.root) and \
                general.root == specialization.root:
            map1 = InferenceRule.formula_specialization_map(general.first, specialization.first)
            map2 = InferenceRule.formula_specialization_map(general.second, specialization.second)
            return InferenceRule.merge_specialization_maps(map1, map2)

        # else, no fitting between the two formulae
        return None
        # Task 4.5b

    def specialization_map(self, specialization: InferenceRule) -> \
            Union[SpecializationMap, None]:
        """Computes the minimal specialization map by which the current
        inference rule specializes to the given specialization.

        Parameters:
            specialization: specialization for which to compute the map.

        Returns:
            The computed specialization map, or ``None`` if `specialization` is
            in fact not a specialization of the current rule.
        """
        assumptions = self.assumptions
        s_assumptions = specialization.assumptions
        # check if there is an equal number of assumptions in both rules
        if len(assumptions) == len(s_assumptions):
            specialization_map = {}
            # go over all assumptions in the two inference rules and check if
            # the s_assumption[i] is assumption[i] that was specialized
            for i in range(len(assumptions)):
                f_specialization_map = InferenceRule.formula_specialization_map(assumptions[i], s_assumptions[i])
                specialization_map = InferenceRule.merge_specialization_maps(
                        specialization_map, f_specialization_map)
                if not specialization_map:  # the map is None
                    return None

            f_specialization_map = InferenceRule.formula_specialization_map(
                self.conclusion, specialization.conclusion)
            specialization_map = InferenceRule.merge_specialization_maps(specialization_map, f_specialization_map)

            return specialization_map

        else:  # different number of assumptions in the two inference rules
            return None

        # Task 4.5c

    def is_specialization_of(self, general: InferenceRule) -> bool:
        """Checks if the current inference rule is a specialization of the given
        inference rule.

        Parameters:
            general: non-specialized inference rule to check.

        Returns:
            ``True`` if the current inference rule is a specialization of
            `general`, ``False`` otherwise.
        """
        return general.specialization_map(self) is not None

@frozen
class Proof:
    """A frozen deductive proof, comprised of a statement in the form of an
    inference rule, a set of inference rules that may be used in the proof, and
    a proof in the form of a list of lines that prove the statement via these
    inference rules.

    Attributes:
        statement (`InferenceRule`): the statement of the proof.
        rules (`~typing.AbstractSet`\\[`InferenceRule`]): the allowed rules of
            the proof.
        lines (`~typing.Tuple`\\[`Line`]): the lines of the proof.
    """
    statment: InferenceRule
    rules: FrozenSet[InferenceRule]
    lines: Tuple[Proof.Line, ...]

    def __init__(self, statement: InferenceRule,
                 rules: AbstractSet[InferenceRule],
                 lines: Iterable[Proof.Line]) -> None:
        """Initializes a `Proof` from its statement, allowed inference rules,
        and lines.

        Parameters:
            statement: the statement for the proof.
            rules: the allowed rules for the proof.
            lines: the lines for the proof.
        """
        self.statement = statement
        self.rules = frozenset(rules)
        self.lines = tuple(lines)

    @frozen
    class Line:
        """An immutable line in a deductive proof, comprised of a formula which
        is either justified as an assumption of the proof, or as the conclusion
        of a specialization of an allowed inference rule of the proof, the
        assumptions of which are justified by previous lines in the proof.

        Attributes:
            formula (`~propositions.syntax.Formula`): the formula justified by
                the line.
            rule (`~typing.Optional`\\[`InferenceRule`]): the inference rule out
                of those allowed in the proof, a specialization of which
                concludes the formula, or ``None`` if the formula is justified
                as an assumption of the proof.
            assumptions
                (`~typing.Optional`\\[`~typing.Tuple`\\[`int`]): a tuple of zero
                or more indices of previous lines in the proof whose formulae
                are the respective assumptions of the specialization of the rule
                that concludes the formula, if the formula is not justified as
                an assumption of the proof.
        """
        formula: Formula
        rule: Optional[InferenceRule]
        assumptions: Optional[Tuple[int, ...]]

        def __init__(self, formula: Formula,
                     rule: Optional[InferenceRule] = None,
                     assumptions: Optional[Iterable[int]] = None) -> None:
            """Initializes a `~Proof.Line` from its formula, and optionally its
            rule and indices of justifying previous lines.

            Parameters:
                formula: the formula to be justified by this line.
                rule: the inference rule out of those allowed in the proof, a
                    specialization of which concludes the formula, or ``None``
                    if the formula is to be justified as an assumption of the
                    proof.
                assumptions: an iterable over indices of previous lines in the
                    proof whose formulae are the respective assumptions of the
                    specialization of the rule that concludes the formula, or
                    ``None`` if the formula is to be justified as an assumption
                    of the proof.
            """
            assert (rule is None and assumptions is None) or \
                   (rule is not None and assumptions is not None)
            self.formula = formula
            self.rule = rule
            if assumptions is not None:
                self.assumptions = tuple(assumptions)

        def __repr__(self) -> str:
            """Computes a string representation of the current proof line.

            Returns:
                A string representation of the current proof line.
            """
            if self.rule is None:
                return str(self.formula)
            else:
                return str(self.formula) + ' Inference Rule ' + \
                       str(self.rule) + \
                       ((" on " + str(self.assumptions))
                        if len(self.assumptions) > 0 else '')

        def is_assumption(self) -> bool:
            """Checks if the current proof line is justified as an assumption of
            the proof.

            Returns:
                ``True`` if the current proof line is justified as an assumption
                of the proof, ``False`` otherwise.
            """
            return self.rule is None

    def __repr__(self) -> str:
        """Computes a string representation of the current proof.

        Returns:
            A string representation of the current proof.
        """
        r = 'Proof for ' + str(self.statement) + ' via inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number: int) -> Union[InferenceRule, None]:
        """Computes the inference rule whose conclusion is the formula justified
        by the specified line, and whose assumptions are the formulae justified
        by the lines specified as the assumptions of that line.

        Parameters:
            line_number: index of the line according to which to construct the
                inference rule.

        Returns:
            The constructed inference rule, with assumptions ordered in the
            order of their indices in the specified line, or ``None`` if the
            specified line is justified as an assumption.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]
        if line.is_assumption():
            return None
        # else, this line is a conclusion
        assumptions = list()
        for i in line.assumptions:
            assumptions.append(self.lines[i].formula)

        assumptions = tuple(assumptions)
        return InferenceRule(assumptions, line.formula)
        # Task 4.6a

    def is_line_valid(self, line_number: int) -> bool:
        """Checks if the specified line validly follows from its justifications.

        Parameters:
            line_number: index of the line to check.

        Returns:
            If the specified line is justified as an assumption, then ``True``
            if the formula justified by this line is an assumption of the
            current proof, ``False`` otherwise. Otherwise (i.e., if the
            specified line is justified as a conclusion of an inference rule),
            then ``True`` if and only if all of the following hold:

            1. The rule specified for that line is one of the allowed inference
               rules in the current proof.
            2. Some specialization of the rule specified for that line has
               the formula justified by that line as its conclusion, and the
               formulae justified by the lines specified as the assumptions of
               that line (in the order of their indices in this line) as its
               assumptions.
        """
        assert line_number < len(self.lines)
        line = self.lines[line_number]
        line_rule = self.rule_for_line(line_number)
        if line_rule:  # line_rule is an Inference rule
            # check if the assumptions appear before the conclusion
            for assumption in line.assumptions:
                if assumption >= line_number:
                    return False
            return line_rule.is_specialization_of(line.rule) and line.rule in self.rules
        else:  # line is an assumption
            formula = line.formula
            if formula in self.statement.assumptions:
                return True
            return False
        # Task 4.6b

    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # check if each line of the proof is valid
        for line_number in range(len(self.lines)):
            if not self.is_line_valid(line_number):
                return False
        # check if the last line's formula is the same as the wanted conclusion
        if self.lines[-1].formula == self.statement.conclusion:
            return True
        return False
        # Task 4.6c

# Chapter 5 tasks

def prove_specialization(proof: Proof, specialization: InferenceRule) -> Proof:
    """Converts the given proof of an inference rule into a proof of the given
    specialization of that inference rule.

    Parameters:
        proof: valid proof to convert.
        specialization: specialization of the conclusion of the given proof.

    Returns:
        A valid proof of the given specialization via the same inference rules
        as the given proof.
    """
    assert proof.is_valid()
    assert specialization.is_specialization_of(proof.statement)

    specialization_map = InferenceRule.specialization_map(
        proof.statement, specialization)
    # get the lines of the proof
    lines = list()
    for line in proof.lines:
        substituted_f = Formula.substitute_variables(line.formula, specialization_map)
        if line.is_assumption():
            lines.append(Proof.Line(substituted_f))
        else:
            lines.append(Proof.Line(substituted_f, line.rule, line.assumptions))
    lines = tuple(lines)

    return Proof(specialization, proof.rules, lines)
    # Task 5.1

def inline_proof_once(main_proof: Proof, line_number: int, lemma_proof: Proof) \
    -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating the usage of (a specialization of)
    that "lemma" rule in the specified line in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        line: index of the line in `main_proof` that should be replaced.
        lemma_proof: valid proof of the inference rule of the specified line (an
            allowed inference rule of `main_proof`).

    Returns:
        A valid proof obtained by replacing the specified line in `main_proof`
        with a full (specialized) list of lines proving the formula of the
        specified line from the lines specified as the assumptions of that line,
        and updating line indices specified throughout the proof to maintain the
        validity of the proof. The set of allowed inference rules in the
        returned proof is the union of the rules allowed in the two given
        proofs, but the "lemma" rule that is used in the specified line in
        `main_proof` is no longer used in the corresponding lines in the
        returned proof (and thus, this "lemma" rule is used one less time in the
        returned proof than in `main_proof`).
    """
    assert main_proof.lines[line_number].rule == lemma_proof.statement
    assert lemma_proof.is_valid()

    replace_line = main_proof.lines[line_number]
    rules = main_proof.rules.union(lemma_proof.rules)
    specialized_lemma = prove_specialization(lemma_proof, main_proof.rule_for_line(line_number))

    lines = list()
    for i in range(line_number):
        lines.append(main_proof.lines[i])

    count = 0  # the place of the current index to assumption
    for line in specialized_lemma.lines:
        if line.is_assumption():
            # There might be an assumption that appears more than once in a row
            while main_proof.lines[replace_line.assumptions[count]].formula != line.formula:
                count += 1
            lines.append(main_proof.lines[replace_line.assumptions[count]])

        else:
            line_assumptions = [assumption + line_number for assumption in
                                line.assumptions]
            lines.append(Proof.Line(line.formula, line.rule, tuple(line_assumptions)))

    # add the rest of the lines
    lemma_length = len(lemma_proof.lines)
    for i in range(line_number+1, len(main_proof.lines)):
        line = main_proof.lines[i]
        if line.is_assumption():
            lines.append(line)
        else:
            new_assumptions = list()
            for assumption in line.assumptions:
                if assumption < line_number:
                    new_assumptions.append(assumption)
                else:  # assumption is after line_number
                    new_assumptions.append(assumption + lemma_length - 1)
            lines.append(Proof.Line(line.formula, line.rule, tuple(new_assumptions)))

    return Proof(main_proof.statement, rules, lines)
    # Task 5.2a

def inline_proof(main_proof: Proof, lemma_proof: Proof) -> Proof:
    """Inlines the given proof of a "lemma" inference rule into the given proof
    that uses that "lemma" rule, eliminating all usages of (any specialization
    of) that "lemma" rule in the latter proof.

    Parameters:
        main_proof: valid proof to inline into.
        lemma_proof: valid proof of one of the allowed inference rules of
            `main_proof`.

    Returns:
        A valid proof obtained from `main_proof` by inlining (an appropriate
        specialization of) `lemma_proof` in lieu of each line that specifies the
        "lemma" inference rule proved by `lemma_proof` as its justification. The
        set of allowed inference rules in the returned proof is the union of the rules
        allowed in the two given proofs but without the "lemma" rule proved by
        `lemma_proof`.
    """
    lemma_length = len(lemma_proof.lines)
    current_proof = main_proof
    proof_length = len(current_proof.lines)
    line_number = 0
    # go over each lemma conclusion line and replace it with the lemma's proof
    while line_number < proof_length:
        if current_proof.lines[line_number].rule == lemma_proof.statement:
            current_proof = inline_proof_once(current_proof, line_number, lemma_proof)
            proof_length += lemma_length - 1
            line_number += lemma_length
        else:
            line_number += 1

    # remove the lemma's statement from the rules
    rules = current_proof.rules.difference({lemma_proof.statement})

    return Proof(current_proof.statement, rules, current_proof.lines)

    # Task 5.2b
