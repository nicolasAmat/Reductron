"""
Presbuger Module

This file is part of Reductron.

Reductron is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Reductron is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Reductron. If not, see <https://www.gnu.org/licenses/>.
"""

from __future__ import annotations

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import operator
import re
import sys
from abc import ABC, abstractmethod
from collections import deque
from typing import Optional, Sequence

TRANSLATION_COMPARISON_OPERATORS = {
    '=': operator.eq,
    '<=': operator.le,
    '>=': operator.ge,
    '<': operator.lt,
    '>': operator.gt,
    'distinct': operator.ne
}

NEGATION_COMPARISON_OPERATORS = {
    '=': 'distinct',
    '<=': '>',
    '>=': '<',
    '<': '>=',
    '>': '<=',
    'distinct': '='
}

COMMUTATION_COMPARISON_OPERATORS = {
    '=': '=',
    '<=': '>=',
    '>=': '<=',
    '<': '>',
    '>': '<',
    'distinct': 'distinct'
}

NEGATION_BOOLEAN_OPERATORS = {
    'and': 'or',
    'or': 'and'
}

BOOLEAN_OPERATORS_TO_FST = {
    'and': '&&',
    'or': '||',
    'not': '!'
}

LTL_TO_BOOLEAN_OPERATORS = {
    '-': 'not',
    '/\\': 'and',
    '\\/': 'or'
}


class Presburger:
    """ Presburger formula.

    Attributes
    ----------
    places : set of str
        Set of places.
    identifier : str
        Associated identifier.
    additional_vars : list of str
        Additional variables in E.
    F: Expression, optional
        Formula.
    """

    def __init__(self, filename: str, places: set[str], identifier: str) -> None:
        """ Initializer.

        Parameters
        ----------
        filename : str
            Path to the net file.
        places : set of places
            Set of places.
        identifier : str
            Associated identifier.
        """
        self.places: set[str] = places
        self.identifier: str = identifier

        self.additional_vars: list[str] = []

        self.F: Optional[Expression] = None

        self.parse_coherency_constraint(filename)

    def __str__(self) -> str:
        """ Formula to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return str(self.F)

    def smtlib(self, k: Optional[int] = None) -> str:
        """ Assert the Formula.

        Note
        ----
        Debugging method.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return self.F.smtlib(k)

    def smtlib_declare(self) -> list[str]:
        return self.additional_vars

    def fast(self) -> str:
        return ' && '.join(map(lambda pl: "({} = K_{})".format(pl, pl), self.places)) + ' && ' + self.F.fast()

    def fast_variables(self) -> list[str]:
        return ["K_{}".format(pl, pl) for pl in self.places]

    def parse_coherency_constraint(self, filename: str) -> None:
        """ Parse coherency constraint.

        Parameters
        ----------
        filename: : str
            Path to the net file.
        """
        try:
            with open(filename, 'r') as fp:
                formula = "T"
                for line in fp.readlines():
                    if "# Constraint:" in line:
                        formula = line.rstrip('\n').replace("# Constraint:", '')
                        break
                self.parse_formula(formula)
            fp.close()
        except FileNotFoundError as e:
            sys.exit(e)

    def parse_formula(self, formula: str) -> None:
        """  parser.

        Parameters
        ----------
        formula : str
            Formula (Tina format).

        Returns
        -------
        Expression
            Parsed formula.
        """
        def _tokenize(s):
            tokens = []
            buffer, last = "", ""
            open_brace = False

            for c in s:

                if c == ' ':
                    continue

                elif (c == '/' and last == '\\') or (c == '\\' and last == '/'):
                    if buffer:
                        tokens.append(buffer)
                    tokens.append(last + c)
                    buffer, last = "", ""

                elif (c == '-' and not open_brace) or c in ['(', ')']:
                    if last:
                        tokens.append(buffer + last)
                    tokens.append(c)
                    buffer, last = "", ""

                elif c == '{':
                    open_brace = True

                elif c == '}':
                    open_brace = False

                else:
                    buffer += last
                    last = c

            if buffer or last:
                tokens.append(buffer + last)

            return tokens

        def _member_constructor(member):
            places, additional_variables, integer_constant, multipliers = [], [], 0, {}
            for element in member.split('+'):
                if element.isnumeric():
                    integer_constant += int(element)
                else:
                    split_element = element.split('*')
                    variable = split_element[-1]
                    if variable not in self.places:
                        additional_variables.append(variable)
                        self.additional_vars.append(variable)
                    else:
                        places.append(variable)

                    if len(split_element) > 1:
                        multipliers[variable] = int(split_element[0])

            if places or additional_variables:
                return TokenCount(places, additional_variables, multipliers)
            else:
                return IntegerConstant(integer_constant)

        # Number of opened parenthesis (not close)
        open_parenthesis = 0

        # Stacks: operators and operands
        stack_operator: deque[tuple[str, int]] = deque()
        stack_operands: deque[list[Expression]] = deque([[]])

        # Current operator
        current_operator = None

        # Parse atom
        parse_atom = False

        for token in _tokenize(formula):

            if token in ['', ' ']:
                continue

            if token in ['-', '/\\', '\\/']:
                # Get the current operator
                token_operator = LTL_TO_BOOLEAN_OPERATORS[token]

                if current_operator:
                    # If the current operator is different from the previous one, construct the previous sub-formula
                    if current_operator != token_operator:
                        stack_operands[-1] = [StateFormula(
                            stack_operands[-1], stack_operator.pop()[0])]
                else:
                    # Add the current operator to the stack
                    stack_operator.append((token_operator, open_parenthesis))
                    current_operator = token_operator

            elif token == '(':
                # Increment the number of parenthesis
                open_parenthesis += 1

                # Add new current operands list
                stack_operands.append([])

                # Reset the last operator
                current_operator = None

            elif token == ')':
                # Fail if no open parenthesis previously
                if not open_parenthesis:
                    raise ValueError("Unbalanced parentheses")

                # Decrease the number of open parenthesis
                open_parenthesis -= 1

                # Add to the previous list
                operands = stack_operands.pop()
                if current_operator:
                    stack_operands[-1].append(StateFormula(operands,
                                              stack_operator.pop()[0]))
                else:
                    stack_operands[-1].append(operands[0])

                current_operator = stack_operator[-1][0] if stack_operator and stack_operator[-1][-1] == open_parenthesis else None

            elif token in ['T', 'F']:
                # Construct BooleanConstant
                stack_operands[-1].append(BooleanConstant(token == 'T'))

            else:
                # Construct Atom
                if re.search("(<=|>=|<|>|=)", token):
                    if parse_atom:
                        _, operator, right = re.split("(<=|>=|<|>|=)", token)
                        stack_operands[-1].append(
                            Atom(stack_operands[-1].pop(), _member_constructor(right), operator))
                        parse_atom = False

                    else:
                        left, operator, right = re.split(
                            "(<=|>=|<|>|=)", token)
                        stack_operands[-1].append(Atom(_member_constructor(
                            left), _member_constructor(right), operator))
                else:
                    stack_operands[-1].append(_member_constructor(token))
                    parse_atom = True

        if open_parenthesis:
            raise ValueError("Unbalances parentheses")

        if stack_operator:
            operands = stack_operands.pop()
            operator = stack_operator.pop()[0]
            self.F = StateFormula(operands, operator)
        else:
            operands, operator = None, None
            self.F = stack_operands.pop()[0]


class SimpleExpression(ABC):
    """ Simple Expression.

    Note
    ----
    Cannot be evaluated to 'TRUE' or 'FALSE'.
    """

    @abstractmethod
    def __str__(self) -> str:
        """ SimpleExpression to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        pass

    @abstractmethod
    def smtlib(self, k: int = None) -> str:
        """ Assert the SimpleExpression.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        pass

    @abstractmethod
    def fast(self) -> str:
        pass

class Expression(SimpleExpression):
    """ Expression.

    Note
    ----
    Can be evaluated to 'TRUE' or 'FALSE'.
    """
    pass


class StateFormula(Expression):
    """ StateFormula.

    Attributes
    ----------
    operands : list of Expression
        A list of operands.
    operator : str
        A boolean operator (not, and, or).
    """

    def __init__(self, operands: Sequence[Expression], operator: str) -> None:
        """ Initializer.

        Parameters
        ----------
        operands : Sequence[Expression]
            List of operands.
        operator : str
            Operator (not, and, or).

        Raises
        ------
        ValueError
            Invalid operator for a StateFormula.
        """
        self.operands: Sequence[Expression] = operands

        self.operator: str = ''
        if operator in ['not', 'and', 'or']:
            self.operator = operator
        else:
            raise ValueError("Invalid operator for a state formula")

    def __str__(self) -> str:
        if self.operator == 'not':
            return "(not {})".format(self.operands[0])

        text = " {} ".format(self.operator).join(map(str, self.operands))

        if len(self.operands) > 1:
            text = "({})".format(text)

        return text

    def smtlib(self, k: int = None) -> str:
        smt_input = ' '.join(map(lambda operand: operand.smtlib(k), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            smt_input = "({} {})".format(self.operator, smt_input)

        return smt_input

    def fast(self) -> str:
        fast_input = ' {} '.format(BOOLEAN_OPERATORS_TO_FST[self.operator]).join(map(lambda operand: operand.fast(), self.operands))

        if len(self.operands) > 1  or self.operator == 'not':
            fast_input = "({})".format(fast_input)

        if self.operator == 'not':
            fast_input = "! {}".format(fast_input)            

        return fast_input


class Atom(Expression):
    """ Atom.

    Attributes
    ----------
    left_operand : Expression
        Left operand.
    right_operand : Expression
        Right operand.
    operator : str
        Operator (=, <=, >=, <, >, distinct).
    """

    def __init__(self, left_operand: SimpleExpression, right_operand: SimpleExpression, operator: str) -> None:
        """ Initializer.

        Parameters
        ----------
        left_operand : SimpleExpression
            Left operand.
        right_operand : SimpleExpression
            Right operand.
        operator : str
            Operator (=, <=, >=, <, >, distinct).

        Raises
        ------
        ValueError
            Invalid operator for an Atom.
        """
        if operator not in ['=', '<=', '>=', '<', '>', 'distinct']:
            raise ValueError("Invalid operator for an atom")

        self.left_operand: SimpleExpression = left_operand
        self.right_operand: SimpleExpression = right_operand

        self.operator: str = operator

    def __str__(self) -> str:
        return "({} {} {})".format(self.left_operand, self.operator, self.right_operand)

    def smtlib(self, k: int = None) -> str:
        return "({} {} {})".format(self.operator, self.left_operand.smtlib(k), self.right_operand.smtlib(k))

    def fast(self) -> str:
        return "({} {} {})".format(self.left_operand.fast(), self.operator, self.right_operand.fast())


class BooleanConstant(Expression):
    """ Boolean constant.

    Attributes
    ----------
    value : bool
        A boolean constant.
    """

    def __init__(self, value: bool) -> None:
        """ Initializer.

        Parameters
        ----------
        value : bool
            A boolean constant.
        """
        self.value: bool = value

    def __str__(self) -> str:
        return str(self.value)

    def smtlib(self, k: int = None) -> str:
        return str(self).lower()

    def fast(self) -> str:
        return str(self).lower()


class TokenCount(SimpleExpression):
    """ Token count.

    Attributes
    ----------
    places : list of str
        A list of places to sum.
    multipliers : dict of Place: int, optional
        Place multipliers (missing if 1).
    """

    def __init__(self, places: list[str], additional_variables: list[str], multipliers: Optional[dict[str, int]] = None):
        """ Initializer.

        Parameters
        ----------
        places : list of str
            A list of places to sum.
        multipliers : dict of Place: int, optional
            Place multipliers (missing if 1).
        """
        self.places: list[str] = places
        self.additional_variables: list[str] = additional_variables

        self.multipliers: dict[str, int] = multipliers

    def __str__(self) -> str:
        text = ' + '.join(map(lambda pl: pl if self.multipliers is None or pl not in self.multipliers else "({}.{})".format(self.multipliers[pl], pl), self.places + self.additional_variables))

        if len(self.places) + len(self.additional_variables) > 1:
            text = "({})".format(text)

        return text

    def smtlib(self, k: int = None) -> str:
        def place_smtlib(pl, k):
            smtlib = pl if k is None else "{}@{}".format(pl, k)
            return  smtlib if self.multipliers is None or pl not in self.multipliers else "(* {} {})".format(smtlib, self.multipliers[pl])

        def variable_smtlib(var):
            return var if self.multipliers is None or var not in self.multipliers else "(* {} {})".format(var, self.multipliers[var])

        smt_input = ' '.join([' '.join(map(lambda pl: place_smtlib(pl, k), self.places)), ' '.join(map(lambda var: variable_smtlib(var), self.additional_variables))])

        if len(self.places) + len(self.additional_variables) > 1:
            smt_input = "(+ {})".format(smt_input)

        return smt_input

    def fast(self) -> str:
        fast_input = ' + '.join(map(lambda pl: "K_{}".format(pl) if self.multipliers is None or pl not in self.multipliers else "K_{} * {}".format(pl.id, self.multipliers[pl]), self.places + self.additional_variables))

        if len(self.places) > 1:
            fast_input = "({})".format(fast_input)

        return fast_input


class IntegerConstant(SimpleExpression):
    """ Integer constant.

    Attributes
    ----------
    value : int
        Constant.
    """

    def __init__(self, value: int) -> None:
        """ Initializer.

        Parameters
        ----------
        value : int
            Constant.
        """
        self.value = value

    def __str__(self) -> str:
        return str(self.value)

    def smtlib(self, k: int = None) -> str:
        return str(self)

    def fast(self) -> str:
        return str(self)


class ArithmeticOperation(SimpleExpression):
    """ Arithmetic Operation.

    Attributes
    ----------
    operands : list of 
        A list of operands.
    operator : str
        An operator ('+', '*').
    """

    def __init__(self, operands: list[SimpleExpression], operator: str) -> None:
        """ Initializer.

        Parameters
        ----------
        operands : list of 
            A list of operands.
        operator : str
            An operator (+, *).

        Raises
        ------
        ValueError
            Invalid operator for an ArithmeticOperation.
        """
        if operator not in ['+', '*']:
            raise ValueError("Invalid operator for an arithmetic operation")

        self.operands: list[SimpleExpression] = operands
        self.operator: str = operator

    def __str__(self) -> str:
        return "(" + " {} ".format(self.operator).join(map(str, self.operands)) + ")"

    def smtlib(self, k: int = None) -> str:
        smt_input = ' '.join(map(lambda operand: operand.smtlib(k), self.operands))
        return "({} {})".format(self.operator, smt_input)

    def fast(self) -> str:
        fast_input = ' {} '.format(self.operator).join(map(lambda operand: operand.fast(), self.operands))
        return "({} {})".format(self.operator, fast_input)


