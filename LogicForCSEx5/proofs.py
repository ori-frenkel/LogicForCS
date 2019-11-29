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

NOT_SPECIALISATION = 1
"""
    helper function for formula_specialization_map
input:
    obj1 - the general formula
    obj2 - the specialisation of obj1
    dict - empty dict to add the mapping that make obj2 specialisation of obj1
output:    
    return NOT_SPECIALISATION if obj2 is not specialisation of obj1
    else, return nothing (and update the dict to the mapping that make 
    obj2 specialisation of obj1
"""

"""
This function gets a list of formula - assumptions
and connect it by '&' (and) and connect the conclusion with '->'
and return it as one formula 
"""
def specialization_map_helper(list_of_assumptions, conclusion):
    to_return = list_of_assumptions
    first = True
    for formula in list_of_assumptions:
        if first:
            to_return = formula
            first = False
        else:
            to_return = Formula('&',to_return, formula)
    if not first:
        return Formula('->',to_return, conclusion)
    else:
        return conclusion

"""
Traverse the tree in preorder and find the minimal mapping between 
obj1( general formula and it's specialization - obj2)  
"""
def preorder_traverse(obj1 : Formula, obj2 : Formula, dict):
    if obj1 is not None and obj2 is not None:
        if obj1.root != obj2.root:
            if not is_variable(obj1.root):
                return NOT_SPECIALISATION
            else:
                # case where the same variable gets two different values
                if obj1.root in dict and dict[obj1.root] != obj2:
                    return NOT_SPECIALISATION
                else:
                    dict.update({obj1.root : obj2})
        elif is_variable(obj1.root):
            # case where the same variable gets two different values
            if obj1.root in dict and dict[obj1.root] != obj2:
                return NOT_SPECIALISATION
            else:
                dict.update({obj1.root : Formula(obj2.root)})
        try:
            if preorder_traverse(obj1.first, obj2.first, dict) == \
                    NOT_SPECIALISATION:
                return NOT_SPECIALISATION
        except AttributeError:
            pass

        try:
            if preorder_traverse(obj1.second, obj2.second, dict) == \
                    NOT_SPECIALISATION:
                return NOT_SPECIALISATION
        except AttributeError:
            pass

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
        # Task 4.1
        var_set = set()
        # adding all the variables in the assumptions
        for formula in self.assumptions:
            for var in formula.variables():
                var_set.add(var)
        # adding all the variables in the conclusion
        for var in self.conclusion.variables():
            var_set.add(var)
        return var_set

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
        # Task 4.4
        assumption_tuple = list()
        for assumption in self.assumptions:
            assumption_tuple.append(
                assumption.substitute_variables(specialization_map))

        substitute_conclusion =  self.conclusion.substitute_variables(
                                                        specialization_map)

        return InferenceRule(assumption_tuple, substitute_conclusion)


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
        # Task 4.5a
        if specialization_map1 is None or specialization_map2 is None:
            return None
        merged_dict = dict()
        for key, value in specialization_map1.items():
            if key in specialization_map2:
                # if both dict has same key but different value, return None
                if value != specialization_map2[key]:
                    return None
                else:
                    # if both keys has same key and same value add this to the
                    #  merged dict
                    merged_dict.update({key: value})
            else:
                # add all the keys that in dict1 but not in dict 2
                merged_dict.update({key: value})
        # add all the key that in dict2 but not in dict 1
        for key,value in specialization_map2.items():
            if key not in specialization_map1:
                merged_dict.update({key: value})
        return merged_dict
        
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
        # Task 4.5b
        my_dict = dict()
        if preorder_traverse(general, specialization, my_dict) ==\
                NOT_SPECIALISATION:
            return None
        return my_dict

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
        # Task 4.5c
        # if one conclusion require different number of assumption from the
        # other conclusion, than it cant be specialization of one another
        if len(self.assumptions) != len(specialization.assumptions):
            return None
        general = specialization_map_helper(self.assumptions, self.conclusion)
        my_specialization = specialization_map_helper(
            specialization.assumptions, specialization.conclusion)

        return self.formula_specialization_map(general, my_specialization)


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

"""
Input:
lst_of_assumptions_line - list of line of assumptions that needed in order to
                          prove the current line
curr_line - the index of the current line
return:
    True if all the assumptions that the current line is based on comes before
    the current line, False other wise.
"""
def valid_index_assumptions(lst_of_assumptions_line, curr_line):
    for line_index in lst_of_assumptions_line:
        if line_index >= curr_line:
            return False
    return True


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
        # Task 4.6a
        # return None if the specified line is justified as an assumption.
        if self.lines[line_number].is_assumption():
            return None
        # else, return InferenceRule with all of the assumption of the given
        # line, and the conclusion (which is the given line)
        assumption_to_return = list()
        for assumption_line_index in self.lines[line_number].assumptions:
            assumption_to_return.append(self.lines[assumption_line_index].formula)
        return InferenceRule(assumption_to_return, self.lines[line_number].formula)

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
               that line (in the or der of their indices in this line) as its
               assumptions.
        """
        assert line_number < len(self.lines)
        # Task 4.6b
        # if its assumption
        if self.lines[line_number].is_assumption():
            # than it must be assumption in the statement
            if self.lines[line_number].formula in self.statement.assumptions:
                return True
            else:
                return False
        else:
            # 1.checking its rule are possible rule (in self.rules)
            # 2.checking that all of the assumptions come before the line that
            # need them
            # 3. checking from specialization
            if self.lines[line_number].rule in self.rules and \
                    valid_index_assumptions(
                        self.lines[line_number].assumptions, line_number) \
                and self.rule_for_line(line_number).is_specialization_of(self.lines[line_number].rule):
                return True
        return False


        
    def is_valid(self) -> bool:
        """Checks if the current proof is a valid proof of its claimed statement
        via its inference rules.

        Returns:
            ``True`` if the current proof is a valid proof of its claimed
            statement via its inference rules, ``False`` otherwise.
        """
        # Task 4.6c
        # if one of the lines is invalid than the proof is invalid.
        for line_index in range(len(self.lines)):
            if not self.is_line_valid(line_index):
                return False
        if self.statement.conclusion != self.lines[len(self.lines) - 1].formula:
             return False
        return True
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
    # Task 5.1

    # the minimal specialization map by which the given formula
    # specializes to the given specialization Inference Rule
    map_of_specialization = InferenceRule(proof.statement.assumptions,
                                        proof.statement.conclusion).specialization_map(specialization)

    # return the specialization of the proof statement
    specialization_statement = proof.statement.specialize(map_of_specialization)
    new_lines = []
    for l_line in proof.lines:
        if l_line.is_assumption():
            new_lines.append(Proof.Line(l_line.formula.substitute_variables(map_of_specialization)))
        else:
            new_formula = l_line.formula.substitute_variables(map_of_specialization)
            new_lines.append(Proof.Line(new_formula, l_line.rule, l_line.assumptions))

    return Proof(specialization_statement,proof.rules, new_lines)

# getting array and shift all the numbers inside by 'shift_by'
def array_number_adder(arr, shift_by, line_number, only_after_shift_by_line = False):
    l_array = list()
    for i in range(len(arr)):
        if only_after_shift_by_line and arr[i] < line_number:
            l_array.append(arr[i])
            continue
        l_array.append(arr[i] + shift_by)
    return l_array

# part 3 from guidance - shift all the assumption's line (after line_number)
# shift all the assumption line accordingly -
# if line is before the changes : stays the same (before line_number)
# if line after the changes, add to the number line, the shift that needed
def helper_part3(new_lines, shift_by : int, curr_line : Proof.Line, line_number,
                 shift_only_num_after_shift_by = False):

    try:
        if curr_line.rule is None or curr_line.rule is not None:
            new_lines.append(Proof.Line(curr_line.formula,curr_line.rule,
                                        array_number_adder(
                                        curr_line.assumptions, shift_by,
                                        line_number,
                                        shift_only_num_after_shift_by)))
    except AttributeError:
        new_lines.append(Proof.Line(curr_line.formula))

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
    # Task 5.2a
    spec_lemma = prove_specialization(lemma_proof, main_proof.rule_for_line(line_number))

    # spec_lemma = prove_specialization(lemma_proof, main_proof.lines[line_number].rule.specialization_map(lemma_proof.statement.conclusion))
    # combine rule minus lemma statement
    total_rules = list()
    for rule in main_proof.rules:
        total_rules.append(rule)
    for rule in lemma_proof.rules:
        total_rules.append(rule)
    # if lemma_proof.statement in total_rules:
    #     total_rules.remove(lemma_proof.statement)

    new_lines = list()
    # same n-1 lines (part a from guidance)
    for idx,line in enumerate(main_proof.lines):
        if idx < line_number:
            new_lines.append(line)
        # part b from guidance
        elif idx == line_number:
            for idx1,lemma_line in enumerate(spec_lemma.lines):
                if lemma_line.is_assumption():
                    # if the line is assumption of the main proof, can copy it as is
                    if lemma_line in main_proof.statement.assumptions:
                        new_lines.append(lemma_line)
                    else:
                        # shift only the assumption line accordingly
                        for line_in_assumption_idx in line.assumptions:
                            if main_proof.lines[line_in_assumption_idx].formula == lemma_line.formula:
                                helper_part3(new_lines, line_number ,
                                             main_proof.lines[line_in_assumption_idx],
                                             line_number, True)
                                break
                else:
                    helper_part3(new_lines, line_number, lemma_line, line_number)
        else: # idx > line number (only need to shift the assumption line num
            shift_by = len(lemma_proof.lines) - 1
            # shift only the number line that bigger the line_number
            # (and shift by len of assumption proof)
            helper_part3(new_lines, shift_by, line, line_number, True)
    return Proof(main_proof.statement, total_rules, new_lines)





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
    # Task 5.2b

