# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulae."""

from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen

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
    return s == '&' or s == '|' or s == '->'
    # For Chapter 3:
    # return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}

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
        print("binary is : ", temp)
        list_str[0] = list_str[0][1:]
        print("new one is : ", list_str[0])
        return temp
    # one more binary operator : ->
    elif is_binary(list_str[0][:2]):
        temp = list_str[0][:2]
        list_str[0] = list_str[0][2:]
        return temp
    # in case of failure, and its not a binary
    return None

def str_to_form(list_str):
    if len(list_str[0]) == 0 or list_str[0] == '':
        list_str[0] = EMPTY_INPUT_ERR
        print("None7")
        return None
    # handle case such as '~'
    if is_unary(list_str[0][0:1]) and (list_str[0][1:] == '' or list_str[0][1:] is None):
        print("---------")
        list_str[0] = UNARY_FOLLOWED_BY_NOTHING_ERR
        print("None5")
        return None
    # in unary check if it '~'
    if is_unary(list_str[0][0:1]):
        list_str[0] = list_str[0][1:] # removing what we deal with - '~'
        return Formula("~", str_to_form(list_str))
    # handle case (X binary_operator Y)
    elif list_str[0][0:1] == "(":
        list_str[0] = list_str[0][1:]
        part1 = str_to_form(list_str) # should ve variable or constant
        part2 = handle_binary(list_str)
        part3 = str_to_form(list_str)
        if part1 is None or not (is_valid_propositional_formula(str(part1))):
            list_str[0] = PROPOSITIONAL_FORMULAE_ERR
            return None
        elif part2 is None :
            list_str[0] = OPERATOR_ERR
            return None
        elif part3 is None or not is_valid_propositional_formula(str(part3)):
            list_str[0] = PROPOSITIONAL_FORMULAE_ERR
            return None
        # need to end with ')'
        if len(list_str[0]) == 0 or list_str[0][0] != ")":
            list_str[0] = CLOSED_PARENTHESIS_MISSING_ERR
            print("None4")
            return None
        else:
            list_str[0] = list_str[0][1:] # removing the ')'

        return Formula(part2, part1, part3)
    # if its binary operator, return it. binary operator : & or |
    elif is_binary(list_str[0][0:1]):
        list_str[0] = BINARY_ERR
        return None
    # if all of the remaining is legal variable
    elif is_variable(list_str[0]) or is_constant(list_str[0]):
        temp = list_str[0]
        list_str[0] = ""
        print("remaining is nothing - ''")
        return Formula(temp)
    # part of the remaining is legal variable
    elif is_variable(list_str[0][0]):
        for j,char in enumerate(list_str[0]):
            if j != 0 and not char.isdigit():
                temp = list_str[0][:j]
                list_str[0] = list_str[0][j:]
                print("temp is : ", temp)
                print("2reaming is : ", list_str[0])
                return Formula(temp)
    elif is_constant(list_str[0][0]):
        the_const = list_str[0][0]
        list_str[0] = list_str[0][1:]
        print("The const is : ", the_const)
        print("The remaining is : ", list_str[0])
        return Formula(the_const)
    elif list_str[0][0] == ")":
        # list_str[0] = ''
        # print("here")
        # return None
        #todo : maybe a case where ends with )
        list_str[0] = list_str[0][1:]
    else:
        print("here None")
        list_str[0] = VAR_ERR
        print("None8")
        return None

def str_to_formula(s : str):
    # if(is_constant(s) or )
    if is_unary(s[0]):
        return Formula("~", str_to_formula(s[1:]))
    elif s[0] in ["(", ")"]:
        index = 0
        index1 = 0
        for j,char in enumerate(s):
            if j == 0 and is_constant(char):
                index = 1
                break
            elif j == 0 and not char.isalpha():
                raise ValueError('A very specific bad thing happened.1')
            elif j != 0 and not char.isdigit():
                index = j - 1
                break
        if s[index + 1: index + 2] not in ["|", "&"]:
            index1 = index + 3
        if s[index:index1] not in ["->"]:
            raise ValueError('A very specific bad thing happened.2')
        Formula(str_to_formula(s[:index]), str_to_formula(s[index + 1:index1]), str_to_formula(s[index1 + 1:]))

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
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
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
        # temp1 = str_to_form(list_h)
        # print(temp1.root)
        # first would need to check that the number of
        #  '(' equals to number of ')'
        print(str(str_to_form(list_h)))
        print("The remaining is : ", list_h[0])


    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.

        Parameters:
            s: string to check.

        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        Formula.parse_prefix(s)[0]
        # Task 1.5
        
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

    def substitute_variables(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
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
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3

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
