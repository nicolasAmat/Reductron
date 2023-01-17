"""
Petri Net Module

Input file format: .net
Standard: http://projects.laas.fr/tina//manuals/formats.html

This file is part of Reductron.

Reduction is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Reduction is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Reductron. If not, see <https://www.gnu.org/licenses/>.
"""

from __future__ import annotations

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "nicolas.amat@laas.fr"
__license__ = "GPLv3"
__version__ = "1.0"

import re
import sys
from typing import Optional


MULTIPLIER_TO_INT = {
    'K': 1000,
    'M': 1000000,
    'G': 1000000000,
    'T': 1000000000000,
    'P': 1000000000000000,
    'E': 1000000000000000000
}


class PetriNet:
    """ Petri net.

    Attributes
    ----------
    id : str
        Identifier.
    filename : str
        Petri net filename.
    places : dict of str: Place
        Finite set of places (identified by names).
    transitions : dict of str: Transition
        Finite set of transitions (identified by names).
    silent_transitions: list of Transition
        List of silent transitions.
    """

    def __init__(self, filename: str) -> None:
        """ Initializer.

        Parameters
        ----------
        filename : str
            Petri net filename.
        """
        self.id: str = ""
        self.filename: str = filename

        self.places: dict[str, Place] = {}
        self.transitions: dict[str, Transition] = {}

        self.silent_transitions: list[Transition] = []

        # Parse the `.net` file
        self.parse_net(filename)

    def __str__(self) -> str:
        """ Petri net to .net format.

        Returns
        -------
        str
            .net format.
        """
        text = "net {}\n".format(self.id)
        text += ''.join(map(str, self.transitions.values()))

        return text

    def silent_restriction(self) -> str:
        """ Petri net restricted to silent transitions to .net format.

        Returns
        -------
        str
            .net format.
        """
        text = "net {}\n".format(self.id)
        text += ''.join(map(str, self.places.values()))
        text += ''.join(map(str, self.silent_transitions))

        return text

    def smtlib_declare_places(self, k: Optional[int] = None) -> str:
        """ Declare places.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda pl: pl.smtlib_declare(k), self.places.values()))

    def smtlib_declare_transitions(self) -> str:
        """ Declare transitions.
        
        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda tr: tr.smtlib_declare(), self.transitions.values()))

    def smtlib_transition_relation(self, k: int, eq: bool = True, tr: bool = False) -> str:
        """ Transition relation from places at order k to order k + 1.
        
        Parameters
        ----------
        k : int
            Order.
        eq : bool, optional
            Add EQ(p_k, p_{k+1}) predicate in the transition relation.
        tr : bool, optional
            Add transition ids.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        if not self.places:
            return smt_input

        if tr:
            smt_input += "(declare-const TRACE@{} Int)\n".format(k)

        smt_input += "(assert (or \n"

        if tr:
            smt_input += ''.join(map(lambda it: it[1].smtlib(k, id=it[0]),enumerate(self.transitions.values())))
        else:
            smt_input += ''.join(map(lambda tr: tr.smtlib(k),self.transitions.values()))
        if eq:
            smt_input += "\t(and\n\t\t"
            if tr:
                smt_input += "(= TRACE@{} (-1))\n\t\t".format(k)
            smt_input += ''.join(map(lambda pl: "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k), self.places.values()))
            smt_input += "\n\t)"
        smt_input += "\n))\n"

        return smt_input

    def parse_net(self, filename: str) -> None:
        """ Petri net parser.

        Parameters
        ----------
        filename : str
            Petri net filename (.net format).

        Raises
        ------
        FileNotFoundError
            Petri net file not found.
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    # '#' and ',' forbidden in SMT-LIB
                    content = re.split(r'\s+', line.strip().replace('#', '.').replace(',', '.'))

                    # Skip empty lines and get the first identifier
                    if not content:
                        continue
                    else:
                        element = content.pop(0)
                    
                    # Net id
                    if element == "net":
                        self.id = content[0].replace('{', '').replace('}', '')

                    # Transition arcs
                    if element == "tr":
                        self.parse_transition(content)

                    # Place
                    if element == "pl":
                        self.parse_place(content)
                    
            fp.close()
        except FileNotFoundError as e:
            sys.exit(e)

    def parse_transition(self, content: list[str]) -> None:
        """ Transition parser.

        Parameters
        ----------
        content : list of string
            Content to parse (.net format).
        """
        transition_id = content.pop(0).replace('{', '').replace('}', '')  # '{' and '}' forbidden in SMT-LIB

        if transition_id in self.transitions:
            tr = self.transitions[transition_id]
        else:
            tr = Transition(transition_id, self)
            self.transitions[transition_id] = tr
            if 'tau' in transition_id:
                self.silent_transitions.append(tr)

        content = self.parse_label(content)

        arrow = content.index("->")
        inputs = content[0:arrow]
        outputs = content[arrow + 1:]

        for arc in inputs:
            tr.connected_places.append(self.parse_arc(arc, tr.pre))

        for arc in outputs:
            tr.connected_places.append(self.parse_arc(arc, tr.post))

        tr.normalize()

    def parse_arc(self, content: str, arcs: dict[Place, int]) -> Place:
        """ Arc parser.

        Parameters
        ----------
        content : 
            Content to parse (.net format).
        arcs : dict of Place: int
            Current arcs.

        Returns
        -------

        """
        content = content.replace('{', '').replace('}', '')  # '{' and '}' forbidden in SMT-LIB

        if '*' in content:
            place_id, _, weight_str = content.partition('*')
            weight = self.parse_value(weight_str)
        else:
            place_id = content
            weight = 1

        if place_id not in self.places:
            new_place = Place(place_id)
            self.places[place_id] = new_place

        pl = self.places.get(place_id)
        arcs[pl] = weight

        return pl

    def parse_place(self, content: list[str]) -> None:
        """ Place parser.

        Parameters
        ----------
        content : list of str
            Place to parse (.net format).
        """
        place_id = content.pop(0).replace('{', '').replace(
            '}', '')  # '{' and '}' forbidden in SMT-LIB

        content = self.parse_label(content)

        if place_id not in self.places:
            place = Place(place_id)
            self.places[place_id] = place
        else:
            place = self.places.get(place_id)

    def parse_label(self, content: list[str]) -> list[str]:
        """ Label parser.

        Parameters
        ----------
        content : list of str
            Content to parse (.net format).

        Returns
        -------
        list of str
            Content without labels.

        """
        index = 0
        if content and content[index] == ':':
            label_skipped = content[index + 1][0] != '{'
            index = 2
            while not label_skipped:
                label_skipped = content[index][-1] == '}'
                index += 1
        return content[index:]

    def parse_value(self, content: str) -> int:
        """ Parse integer value.

        Parameters
        ----------
        content : str
            Content to parse (.net format).

        Returns
        -------
        int
            Corresponding integer value.

        Raises
        ------
        ValueError
            Incorrect integer value.

        """
        if content.isnumeric():
            return int(content)

        multiplier = content[-1]

        if multiplier not in MULTIPLIER_TO_INT:
            raise ValueError("Incorrect integer value")

        return int(content[:-1]) * MULTIPLIER_TO_INT[multiplier]


class Place:
    """ Place.

    Attributes
    ----------
    id : str
        An identifier.
    """

    def __init__(self, place_id: str) -> None:
        """ Initializer.

        Parameters
        ----------
        place_id : str
            An identifier.
        """
        self.id: str = place_id

    def __str__(self) -> str:
        """ Place to .net format.

        Returns
        -------
        str
            .net format.
        """
        return "pl {}\n".format(self.id)

    def smtlib(self, k: Optional[int] = None) -> str:
        """ Place identifier.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "{}@{}".format(self.id, k) if k is not None else self.id

    def smtlib_declare(self, k: Optional[int] = None) -> str:
        """ Declare a place.

        Parameters
        ----------
        k : int, optional

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "({} Int)".format(self.smtlib(k))


class Transition:
    """ Transition.

    Attributes
    ----------
    id : str
        An identifier.
    pre: dict of Place: int
        Pre vector (firing condition).
    post: dict of Place: int
        Post vector.
    connected_places: list of Place
        List of the places connected to the transition.
    ptnet: PetriNet
        Associated Petri net.
    """

    def __init__(self, transition_id: str, ptnet: PetriNet) -> None:
        """ Initializer.

        Parameters
        ----------
        transition_id : str
            An identifier.
        ptnet : PetriNet
            Associated Petri net.
        """
        self.id: str = transition_id

        self.pre: dict[Place, int] = {}
        self.post: dict[Place, int] = {}

        self.delta: dict[Place, int] = {}

        self.connected_places: list[Place] = []
        self.ptnet: PetriNet = ptnet

    def __str__(self) -> str:
        """ Transition to textual format.
        
        Returns
        -------
        str
            .net format.
        """
        text = "tr {} ".format(self.id)

        for src, weight in self.pre.items():
            text += ' ' + self.str_arc(src, weight)

        text += ' ->'

        for dest, weight in self.post.items():
            text += ' ' + self.str_arc(dest, weight)

        text += '\n'
        return text

    def str_arc(self, place: Place, weight: int) -> str:
        """ Arc to textual format.

        Parameters
        ----------
        place : place
            Input place.
        weight : int
            Weight of the arc (negative if inhibitor).

        Returns
        -------
        str
            .net format.
        """
        text = place.id

        if weight > 1:
            text += '*' + str(weight)

        return text

    def normalize(self):
        for place in set(self.pre.keys()) | set(self.post.keys()):
            delta = self.post.get(place, 0) - self.pre.get(place, 0)
            if delta != 0:
                self.delta[place] = delta

    def smtlib(self, k: int) -> str:
        """ Transition relation from places at order k to order k + 1.
            
        Parameters
        ----------
        k : int
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = "\t(and\n\t\t"

        # Firing condition on input places
        for pl, weight in self.pre.items():
            smt_input += "(>= {}@{} {})".format(pl.id, k, weight)
        smt_input += "\n\t\t"

        # Update places
        for pl, weight in self.delta.items():
            smt_input += "(= {}@{} ({} {}@{} {}))".format('-' if weight < 0 else '+', pl.id, k + 1, pl.id, k, abs(weight))
        smt_input += "\n\t\t"

        # Unconnected places must not be changed
        for pl in self.ptnet.places.values():
            if pl not in self.connected_places or (pl in self.tests and pl not in self.inputs and pl not in self.outputs):
                smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)

        smt_input += "\n\t)\n"

        return smt_input

    def smtlib_declare(self) -> str:
        """ Declare a transition.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "({} Int)".format(self.id)


class Sequence:
    """
    """

    def __init__(self, ptnet: PetriNet, id: str, sequence: list[Transition]):
        """ Initializer.
        """
        self.ptnet: PetriNet = ptnet

        # Saturation variables
        self.saturation_variable:str = id

        # Sequence of transitions
        self.sequence = sequence

        self.hurdle = {}
        self.delta = {}

        self.compute_vectors()

    def __str__(self):
        """ Sequence to textual format.
        """
        if not self.sequence:
            return "epsilon"
        else:
            return "({})*".format(' '.join(map(lambda tr: tr.id, self.sequence)))

    def smtlib_declare(self) -> str:
        return "({} Int)".format(self.saturation_variable)

    def smtlib(self, k: int = 0):
        """ States to SMT-LIB format.
        """
        if not self.sequence:
            return "(true)"

        smt_input = "(>= {} 0)".format(self.saturation_variable)

        smt_input += ' '.join(["(>= {} {})".format(pl.smtlib(k), str(hurdle) if self.delta.get(pl) >= 0 else "(+ {} (* {} {}))").format(hurdle, self.saturation_variable, abs(self.delta.get(pl, 0))) for pl, hurdle in self.hurdle.items()])

        smt_input += ' '.join(["(= {} ({} {} (* {} {})))".format(pl.smtlib(k + 1), '-' if delta < 0 else '+', pl.smtlib(k), self.saturation_variable, abs(delta)) for pl, delta in self.delta.items()])
        
        for pl in self.ptnet.places.values():
            if pl not in set.union(*[set(tr.connected_places) for tr in self.sequence]):
                smt_input += "(= {} {})".format(pl.smtlib(k + 1), pl.smtlib(k))

        smt_input = "(and {})".format(smt_input)

        return "(exists ({}) {})".format(self.smtlib_declare(), smt_input)

    def compute_vectors(self):
        for tr in reversed(self.sequence):
            for pl in set(tr.connected_places):
                # H(t.\sigma) = max(H(t), H(\sigma) - \Delta(t))
                self.hurdle[pl] = max(tr.pre.get(pl, 0), self.hurdle.get(pl, 0) - tr.delta.get(pl, 0))
                 # \Delta(t.\sigma) = \Delta(t) + \Delta(\sigma)
                self.delta[pl] = self.delta.get(pl, 0) + tr.delta.get(pl, 0)    

   

