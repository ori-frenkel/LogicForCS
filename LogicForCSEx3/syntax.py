# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulae."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen
import re

VAR = 1
OPERATOR = 2
EMPTY_INPUT_ERR = "The given string in empty"
UNARY_FOLLOWED_BY_NOTHING_ERR = "unary must be followed by valid" \
                                "propositional formulae "
CLOSED_PARENTHESIS_MISSING_ERR = "You have problems with the '(' and ')'" \
                                " check that you put it in the intended way"

PROPOSITIONAL_FORMULAE_ERR = "(X Binary operator Y) X and Y must be valid "\
                              "propositional formulae "

OPERATOR_ERR = "(X operator Y) operator must be a binary operator" \
                " meaning & or | or ->"

BINARY_ERR = "You cant use binary operation in such way, the only allowed " \
             "way is (X Binary_Operator Y) where X and Y"\
             "valid propositional formulae"

VAR_ERR = "Illegal variable"


def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    # return s == '&' or s == '|' or s == '->'
    # For Chapter 3:
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}

# return true if the given string is valid propositional formula
def is_valid_propositional_formula(s: str) -> bool:
    list_str = [s]
    if str_to_form(list_str) is None:
        return False
    return True


def in_order_repr_helper(formula_obj, list_to_return) -> None:
    need_to_close = False # True if need to close the parentheses - ')'
    if formula_obj is None:
        return
    try:
        # case where there is root both left and right son.
        if is_binary(formula_obj.root) and type(formula_obj.first) is Formula\
            and type(formula_obj.second) is Formula:
            list_to_return[0] += "("
            need_to_close = True
        # case where there is root and left son, and no right son,
        # for example ~F
        elif is_unary(formula_obj.root):
                list_to_return[0] += formula_obj.root
                in_order_repr_helper(formula_obj.first, list_to_return)
                return
    except AttributeError:
        pass
    try:
        in_order_repr_helper(formula_obj.first, list_to_return)
    except AttributeError:
        pass
    list_to_return[0] += formula_obj.root
    try:
        in_order_repr_helper(formula_obj.second, list_to_return)
    except AttributeError:
        pass
    if need_to_close:
        list_to_return[0] += ")"

"""
This function traverse the tree, and add to the given set all the
Variables or Operator depending on the given _type
VAR = 1
OPERATOR = 2
"""
def in_order_traverse(formula_obj, set_to_store : Set[str], _type):
    if formula_obj is None:
        return
    try:
        in_order_traverse(formula_obj.first, set_to_store, _type)
    except AttributeError:
        pass

    if _type == VAR and is_variable(formula_obj.root):
        set_to_store.add(formula_obj.root)
    elif _type == OPERATOR and\
            (is_unary(formula_obj.root) or is_binary(formula_obj.root) or\
             is_constant(formula_obj.root)):
        set_to_store.add(formula_obj.root)

    try:
        in_order_traverse(formula_obj.second, set_to_store, _type)
    except AttributeError:
        pass

def in_order_traverse_substitute_variables_helper(formula_obj, dict, lst):
    if formula_obj is None:
        return
    try:
        in_order_traverse_substitute_variables_helper(formula_obj.first, dict, lst)
    except AttributeError:
        pass
    print("Formula Obj is : ", formula_obj)
    if str(formula_obj) in dict:
        print("Change this : ", formula_obj)
        formula_obj = dict[str(formula_obj)]
        print("TO this : ", formula_obj)
        print("Root is : ", lst)
        print("Added this : ", str(formula_obj))
        lst.append(formula_obj)
    else:
        print("Added this : ", str(formula_obj))
        lst.append(formula_obj.root)

    try:
        in_order_traverse_substitute_variables_helper(formula_obj.second, dict, lst)
    except AttributeError:
        pass
    print("The end is : ", str(formula_obj))
    return formula_obj

# check if the given input is None
def check_for_none(_input):
    try:
        if _input is None:
            return True
    except TypeError:
        return False


def is_variable_or_constant(s:str) -> bool:
    if not (is_variable(s) or is_constant(s)):
        return False
    return True

def handle_binary(list_str):
    # if its binary operator, return it. binary operator : & or |
    if is_binary(list_str[0][0:1]):
        temp = list_str[0][:1]
        # print("binary is : ", temp)
        list_str[0] = list_str[0][1:]
        # print("new one is : ", list_str[0])
        return temp
    # one more binary operator : ->
    elif len(list_str[0]) >= 2 and is_binary(list_str[0][:2]):
        temp = list_str[0][:2]
        list_str[0] = list_str[0][2:]
        return temp
    elif len(list_str[0]) >= 3 and is_binary(list_str[0][:3]):
        temp = list_str[0][:3]
        list_str[0] = list_str[0][3:]
        return temp
    # in case of failure, and its not a binary
    return None

# handle the case where the string start with '('
def handle_parenthesis_case(list_str):
    list_str[0] = list_str[0][1:] # removing the '(' from the string
    part1 = str_to_form(list_str)
    part2 = handle_binary(list_str) # should be binary operator
    part3 = str_to_form(list_str)
    if part1 is None or not (is_valid_propositional_formula(str(part1))):
        list_str[0] = PROPOSITIONAL_FORMULAE_ERR
        return None
    elif part2 is None:
        list_str[0] = OPERATOR_ERR
        return None
    elif part3 is None or not is_valid_propositional_formula(str(part3)):
        list_str[0] = PROPOSITIONAL_FORMULAE_ERR
        return None
    # need to end with ')'
    if len(list_str[0]) == 0 or list_str[0][0] != ")":
        list_str[0] = CLOSED_PARENTHESIS_MISSING_ERR
        return None
    else:
        list_str[0] = list_str[0][1:]  # removing the ')'

    return Formula(part2, part1, part3)


# handle the case that it start with unary '~'
def handle_unary(list_str):
    if list_str[0][1:] == '' or list_str[0][1:] is None:
        list_str[0] = UNARY_FOLLOWED_BY_NOTHING_ERR
        return None
    list_str[0] = list_str[0][1:]  # removing what we deal with - '~'
    temp_formula = str_to_form(list_str)
    if temp_formula is None:
        return None
    return Formula("~", temp_formula)

def str_to_form(list_str):
    if len(list_str[0]) == 0 or list_str[0] == '':
        list_str[0] = EMPTY_INPUT_ERR
        return None

    # case where it start with unary '~'
    if is_unary(list_str[0][0:1]):
        return handle_unary(list_str)

    # handle case (X binary_operator Y)
    elif list_str[0][0:1] == "(":
        return handle_parenthesis_case(list_str)

    # if its binary operator, return it. binary operator : & or |
    elif is_binary(list_str[0][0:1]) or is_binary(list_str[0][:2]):
        list_str[0] = BINARY_ERR
        return None

    # if all of the remaining is legal variable
    elif is_variable(list_str[0]) or is_constant(list_str[0]):
        temp = list_str[0]
        list_str[0] = ""
        return Formula(temp)

    # part of the remaining is legal variable
    elif is_variable(list_str[0][0]):
        for j,char in enumerate(list_str[0]):
            if j != 0 and not char.isdigit():
                temp = list_str[0][:j]
                list_str[0] = list_str[0][j:]
                return Formula(temp)
    elif is_constant(list_str[0][0]):
        the_const = list_str[0][0]
        list_str[0] = list_str[0][1:]
        return Formula(the_const)
    elif list_str[0][0] == ")":
        list_str[0] = list_str[0][1:]
    else:
        list_str[0] = VAR_ERR
        return None

def check_for_null(formula):
    first = False
    second = False
    try:
        tmp1 = formula.first
    except AttributeError:
        first = True
    try:
        tmp2 = formula.second
    except AttributeError:
        second = True
    return first, second

# this function check if self.first exist or not, and return the formula
#  according to it (if it does not exist change the dict according to it)
# for example, if formula.right.right does not exist, than we dont need to
# substitute 'p' therefor we send dict without 'p'
def operator_substitute_helper(formula_self, dictt, left_or_right):
    if left_or_right == "left":
        result_check_null = check_for_null(formula_self.first)
        if result_check_null[0] and result_check_null[1]:
            return dictt[str(formula_self.first)]
        elif result_check_null[0] and not result_check_null[1]:
            return dictt[str(formula_self.first)].substitute_variables(
                {'q': formula_self.first.second}, True)
        elif not result_check_null[0] and result_check_null[1]:
            return dictt[str(formula_self.first)].substitute_variables(
                {'p': formula_self.first.first}, True)
        else:
            return dictt[str(formula_self.first)].substitute_variables(
                   {'p': formula_self.first.first, 'q': formula_self.first.second},
                    True)
    else:
        result_check_null = check_for_null(formula_self.second)
        if result_check_null[0] and result_check_null[1]:
            return dictt[str(formula_self.second)]
        elif result_check_null[0] and not result_check_null[1]:
            return dictt[str(formula_self.second)].substitute_variables(
                {'q': formula_self.second.second}, True)
        elif not result_check_null[0] and result_check_null[1]:
            return dictt[str(formula_self.second)].substitute_variables(
                {'p': formula_self.second.first}, True)
        else:
            return dictt[str(formula_self.second)].substitute_variables(
                   {'p': formula_self.second.first, 'q':
                       formula_self.second.second},True)


@frozen
class Formula:
    """An immutable propositional formula in tree representation.

    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.

        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            if type(first) is not Formula:
                print("first is : ", first, "  And root is : ", root)
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            # print("Second is : ", second, "\n And type is : ", str(type(second)))
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        list_to_return = [""]
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        in_order_repr_helper(self, list_to_return)
        return list_to_return[0]

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.

        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        my_set = set([])
        in_order_traverse(self, my_set, VAR)
        return my_set


    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.

        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        my_set = set([])
        in_order_traverse(self, my_set, OPERATOR)
        return my_set

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # Task 1.4
        list_h = [s]
        return (str_to_form(list_h), list_h[0])


    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """

        # Task 1.5
        parsed_ver = Formula.parse_prefix(s)
        if len(parsed_ver[1]) != 0 or parsed_ver[0] is None:
            return False
        return True

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)
        # Task 1.6
        parsed_ver = Formula.parse_prefix(s)
        return parsed_ver[0]

# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.

        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

# Tasks for Chapter 3

    # Helper function for substitute_variables, traverse the tree, and making
    # a new tree, which contain the substitute variables
    def copy_and_substitute_variables(self, dict) -> Formula:
        value = self.root
        left = None
        right = None
        try:
            if self.first is not None:
                if str(self.first) in dict:
                    left = dict[str(self.first)]
                else:
                    left = self.first.copy_and_substitute_variables(dict)
        except AttributeError:
            pass
        try:
            if self.second is not None:
                if str(self.second) in dict:
                    right = dict[str(self.second)]
                else:
                    right = self.second.copy_and_substitute_variables(dict)
        except AttributeError:
            pass
        if value in dict:
            valueInDict = str(dict[value])
            if not (is_variable(valueInDict) or is_binary(valueInDict)
                    or is_constant(valueInDict)):
                return dict[value]
            else:
                value = valueInDict

        return Formula(value, left, right)

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula],
            remove_none = False, var_assert = True) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        if var_assert:
            for variable in substitution_map:
                assert is_variable(variable)
        # Task 3.3
        if remove_none:
            new_dict = dict(substitution_map)
            for key, val in substitution_map.items():
                if val is None:
                    del new_dict[key]
            return self.copy_and_substitute_variables(new_dict)

        return self.copy_and_substitute_variables(substitution_map)


    def copy_and_substitute_operator(self, dict) -> Formula:
        value = self.root
        left = None
        right = None
        try:
            if self.first is not None:
                if str(self.first) in dict:
                   left = operator_substitute_helper(self, dict, "left")
                else:
                    left = self.first.copy_and_substitute_operator(dict)
        except AttributeError:
            pass
        try:
            if self.second is not None:
                if str(self.second) in dict:
                    right =  operator_substitute_helper(self, dict, "right")
                else:
                    right = self.second.copy_and_substitute_operator(dict)
        except AttributeError:
            pass
        if value in dict:
            return dict[value].substitute_variables({'p' : left, 'q' : right}, True)

        return Formula(value, left, right)

    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.

        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.

        Returns:
            The resulting formula.

        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4

        return self.copy_and_substitute_operator(substitution_map)
