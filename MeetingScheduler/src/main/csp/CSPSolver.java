package main.csp;

import static org.junit.Assert.fail;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.List;
import java.util.Objects;
import java.util.*;

/**
 * CSP: Calendar Satisfaction Problem Solver Provides a solution for scheduling
 * some n meetings in a given period of time and according to some unary and
 * binary constraints on the dates of each meeting.
 */

public class CSPSolver {

	// Backtracking CSP Solver
	// --------------------------------------------------------------------------------------------------------------

	/**
	 * Public interface for the CSP solver in which the number of meetings, range of
	 * allowable dates for each meeting, and constraints on meeting times are
	 * specified.
	 * 
	 * @param nMeetings   The number of meetings that must be scheduled, indexed
	 *                    from 0 to n-1
	 * @param rangeStart  The start date (inclusive) of the domains of each of the n
	 *                    meeting-variables
	 * @param rangeEnd    The end date (inclusive) of the domains of each of the n
	 *                    meeting-variables
	 * @param constraints Date constraints on the meeting times (unary and binary
	 *                    for this assignment)
	 * @return A list of dates that satisfies each of the constraints for each of
	 *         the n meetings, indexed by the variable they satisfy, or null if no
	 *         solution exists.
	 */

	public static List<LocalDate> solve(int nMeetings, LocalDate rangeStart, LocalDate rangeEnd,
			Set<DateConstraint> constraints) {

		List<MeetingDomain> meetingDomainList = generateDomains(nMeetings, rangeStart, rangeEnd);
		nodeConsistency(meetingDomainList, constraints);
		arcConsistency(meetingDomainList, constraints);
		List<LocalDate> assignment = getDefaultList(nMeetings);
		List<LocalDate> output = recursiveBacktracking(assignment, nMeetings, meetingDomainList, constraints, 0);
		return output;
	}

	/*
	 * Generates list of meeting domains with Di (meeting domain list index)
	 * corresponding to Meeting Index i.
	 * 
	 * @param n number of meetings to be scheduled
	 * 
	 * @param start date of domain range
	 * 
	 * @param endRange end date of domain range
	 * 
	 * @output List of meeting domains
	 * 
	 */

	private static List<MeetingDomain> generateDomains(int n, LocalDate startRange, LocalDate endRange) {
		List<MeetingDomain> domains = new ArrayList<>();
		while (n > 0) {
			domains.add(new MeetingDomain(startRange, endRange));
			n--;
		}
		return domains;
	}

	/*
	 * HELPER METHOD for solve. This method is used to recursively backtrack all
	 * possible search solutions
	 * 
	 * @param assignment List of LocalDates used for assignment purposes
	 * 
	 * @output List of LocalDates dates for assignment purposes
	 * 
	 */

	public static List<LocalDate> recursiveBacktracking(List<LocalDate> assignment, int nMeetings,
			List<MeetingDomain> meetingDomainList, Set<DateConstraint> constraints, int meetingIndex) {

		if (nMeetings == meetingIndex) {
			return assignment;
		}

		for (LocalDate d : meetingDomainList.get(meetingIndex).domainValues) {
			LocalDate tempDate = d;
			assignment.set(meetingIndex, tempDate);
			if (testSol(assignment, constraints)) {
				List<LocalDate> result = recursiveBacktracking(assignment, nMeetings, meetingDomainList, constraints,
						meetingIndex + 1);
				if (result != null) {
					return result;
				}

			}

			else {
				assignment.set(meetingIndex, null);
			}

		}

		return null;

	}

	/*
	 * HELPER METHOD for solve Initialize list of default null values given
	 * specified number of meetings (=
	 * 
	 * @param nMeetings number of meetings
	 * 
	 * @output List of nulls dictated by the number of meetings
	 */

	public static List<LocalDate> getDefaultList(int nMeetings) {
		List<LocalDate> defAssignment = new ArrayList<>();
		for (int i = 0; i < nMeetings; i++) {
			defAssignment.add(null);
		}
		return defAssignment;

	}

	/*
	 * HELPER METHOD for solve Helper method that checks if all constraints are
	 * satisfied with currentList of LocalDates
	 * 
	 * @param solution list of possible solutions (comprised of local dates)
	 * 
	 * @param constraints set of local date constraints
	 * 
	 * @return Boolean
	 * 
	 */

	public static Boolean testSol(List<LocalDate> assignment, Set<DateConstraint> constraints) {


		LocalDate leftDate = null;
		LocalDate rightDate = null;
		// check each of the constraints
		for (DateConstraint dConstraint : constraints) {

			// leftDate <- retrieve left index
			// rightDate <- retrieve right date / index

			// check if variable relating to constraint is present
			if (assignment.get(dConstraint.L_VAL) != null && dConstraint.L_VAL < assignment.size()) {
				leftDate = assignment.get(dConstraint.L_VAL);
				if (dConstraint.arity() != 1 && assignment.get(((BinaryDateConstraint) dConstraint).R_VAL) != null) {
					rightDate = assignment.get(((BinaryDateConstraint) dConstraint).R_VAL);
				} else if (dConstraint.arity() == 1) {
					rightDate = ((UnaryDateConstraint) dConstraint).R_VAL;
				} else
					continue;
				if (dConstraint.isSatisfiedBy(leftDate, rightDate)) {
					continue;
				}
				return false;
			}

		}
		return true;
	}

	// Filtering Operations
	// --------------------------------------------------------------------------------------------------------------

	/**
	 * Enforces node consistency for all variables' domains given in varDomains
	 * based on the given constraints. Meetings' domains correspond to their index
	 * in the varDomains List.
	 * 
	 * @param varDomains  List of MeetingDomains in which index i corresponds to D_i
	 * @param constraints Set of DateConstraints specifying how the domains should
	 *                    be constrained. [!] Note, these may be either unary or
	 *                    binary constraints, but this method should only process
	 *                    the *unary* constraints!
	 */

	public static void nodeConsistency(List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {

		// make sure only unary constraints are processed in this function
		constraints = getUnaryConstraints(constraints);


		// filter the domains to ensure node consistency
		List<MeetingDomain> outputDomains = new ArrayList<MeetingDomain>();

		for (DateConstraint unaryConstraint : constraints) {
			MeetingDomain currDomain = varDomains.get(unaryConstraint.L_VAL);
			MeetingDomain currDomainCopy = new MeetingDomain(currDomain);
			LocalDate rightDate = ((UnaryDateConstraint) unaryConstraint).R_VAL;
			for (LocalDate domainDate : currDomain.domainValues) {
				LocalDate leftDate = domainDate;

				if (!(unaryConstraint.isSatisfiedBy(leftDate, rightDate))) {
					currDomainCopy.domainValues.remove(domainDate);
				}

			}

			varDomains.get(unaryConstraint.L_VAL).domainValues = currDomainCopy.domainValues;
		}

	}

	/*
	 * HELPER METHOD for nodeConsistency Filters a set of constraints for unary
	 * constraints only
	 * 
	 * @param constraints set of constrants (can be unary or binary)
	 * 
	 * @ouput set of unary constraints
	 */

	private static Set<DateConstraint> getUnaryConstraints(Set<DateConstraint> constraints) {
		Set<DateConstraint> unaryConstraintsOnly = new HashSet<DateConstraint>();
		for (DateConstraint constraint : constraints) {
			if (constraint.ARITY == 1) {
				UnaryDateConstraint unaryConstraint = (UnaryDateConstraint) constraint;
				unaryConstraintsOnly.add(unaryConstraint);
			}
		}

		return unaryConstraintsOnly;
	}

	/**
	 * Enforces arc consistency for all variables' domains given in varDomains based
	 * on the given constraints. Meetings' domains correspond to their index in the
	 * varDomains List.
	 * 
	 * @param varDomains  List of MeetingDomains in which index i corresponds to D_i
	 * @param constraints Set of DateConstraints specifying how the domains should
	 *                    be constrained. [!] Note, these may be either unary or
	 *                    binary constraints, but this method should only process
	 *                    the *binary* constraints using the AC-3 algorithm!
	 */

	public static void arcConsistency(List<MeetingDomain> varDomains, Set<DateConstraint> constraints) {
		Set<Arc> arcSetOriginal = getArcs(constraints);
		Set<Arc> arcSet = getArcs(constraints);

		while (!(arcSet.isEmpty())) {
			Set<Arc> neighborArcs = new HashSet<Arc>();

			for (Arc currArc : arcSet) {

				if (removeInconsistentValues(varDomains, currArc)) {
					neighborArcs.addAll(findAllNeighborArcs(arcSetOriginal, currArc));
				}

			}
			arcSet = neighborArcs;

		}
	}

	/*
	 * HELPER METHOD for arcConsistency Finds all neighboring arcs of a given arc in
	 * an arcSet
	 * 
	 * @param arcSetFinal unchanging list of arcs passed from arcConsistency method
	 * 
	 * @param currArc current Arc that is being examined
	 * 
	 * @output Set of neighboring arcs
	 * 
	 */

	private static Set<Arc> findAllNeighborArcs(Set<Arc> arcSetFinal, Arc currArc) {
		Set<Arc> neighborArcs = new HashSet<Arc>();
		int tailIndex = currArc.TAIL;
		for (Arc arc : arcSetFinal) {
			if (arc.HEAD == tailIndex) {
				neighborArcs.add(arc);
			}
		}
		return neighborArcs;
	}

	/*
	 * HELPER METHOD for arcConsistency Boolean method to remove inconsistent values
	 * from each arc's tail domain
	 * 
	 * @param varDomains list of meeting domains
	 * 
	 * @param currArc current arc that is being examined
	 * 
	 * @ouput true if inconsistent values have been removed
	 * 
	 */

	private static Boolean removeInconsistentValues(List<MeetingDomain> varDomains, Arc currArc) {

		// find respective tail and head domain
		MeetingDomain tailDomain = varDomains.get(currArc.TAIL), headDomain = varDomains.get(currArc.HEAD);

		MeetingDomain tailDomainCopy = new MeetingDomain(tailDomain);
		Boolean removed = false;
		List<Boolean> potentialRemovalFlag = new ArrayList<Boolean>();

		for (LocalDate leftDate : tailDomain.domainValues) {
			for (LocalDate rightDate : headDomain.domainValues) {
				if (currArc.CONSTRAINT.isSatisfiedBy(leftDate, rightDate)) {
					potentialRemovalFlag.add(true);
				} else {
					potentialRemovalFlag.add(false);
				}
			}

			if (!(potentialRemovalFlag.contains(true))) {
				tailDomainCopy.domainValues.remove(leftDate);
				removed = true;
				potentialRemovalFlag.clear();
			}
			potentialRemovalFlag.clear();

		}
		// update varDomains with pruned domains after arc consistency check
		varDomains.get(currArc.TAIL).domainValues = tailDomainCopy.domainValues;

		// inconsistent values has been removed
		return removed;
	}

	/*
	 * HELPER METHOD for arcConsistency for each constraint in a given set of
	 * constraints, create two arcs with tail -> head and head -> tail
	 * 
	 * @param constraints a set of date constraints
	 * 
	 * @output a set of arcs created from only binaryConstraints
	 * 
	 */

	private static Set<Arc> getArcs(Set<DateConstraint> constraints) {

		Set<Arc> arcSet = new HashSet<Arc>();
		// filter so that only binary constraints remain
		constraints = getBinaryConstraints(constraints);

		for (DateConstraint constraint : constraints) {
			BinaryDateConstraint binaryConstraint = (BinaryDateConstraint) constraint;
			BinaryDateConstraint reversedBinaryConstraint = ((BinaryDateConstraint) constraint).getReverse();
			arcSet.add(new Arc(binaryConstraint.L_VAL, binaryConstraint.R_VAL, constraint));
			arcSet.add(
					new Arc(reversedBinaryConstraint.L_VAL, reversedBinaryConstraint.R_VAL, reversedBinaryConstraint));
		}

		return arcSet;
	}

	/*
	 * HELPER METHOD for arcConsistency filters out any non - binary Constraints
	 * given a set of date constraints
	 * 
	 * @param constraints a set of data constraints
	 * 
	 * @output a set of binary constrants only
	 * 
	 */

	private static Set<DateConstraint> getBinaryConstraints(Set<DateConstraint> constraints) {
		Set<DateConstraint> binaryConstraintsOnly = new HashSet<DateConstraint>();
		for (DateConstraint constraint : constraints) {
			if (constraint.ARITY != 1) {
				binaryConstraintsOnly.add((BinaryDateConstraint) constraint);
			}
		}

		return binaryConstraintsOnly;
	}

	/**
	 * Private helper class organizing Arcs as defined by the AC-3 algorithm, useful
	 * for implementing the arcConsistency method. [!] You may modify this class
	 * however you'd like, its basis is just a suggestion that will indeed work.
	 */
	private static class Arc {

		public final DateConstraint CONSTRAINT;
		public final int TAIL, HEAD;

		/**
		 * Constructs a new Arc (tail -> head) where head and tail are the meeting
		 * indexes corresponding with Meeting variables and their associated domains.
		 * 
		 * @param tail Meeting index of the tail
		 * @param head Meeting index of the head
		 * @param c    Constraint represented by this Arc. [!] WARNING: A
		 *             DateConstraint's isSatisfiedBy method is parameterized as:
		 *             isSatisfiedBy (LocalDate leftDate, LocalDate rightDate), meaning
		 *             L_VAL for the first parameter and R_VAL for the second. Be
		 *             careful with this when creating Arcs that reverse direction. You
		 *             may find the BinaryDateConstraint's getReverse method useful
		 *             here.
		 */

		public Arc(int tail, int head, DateConstraint c) {
			this.TAIL = tail;
			this.HEAD = head;
			this.CONSTRAINT = c;
		}

		@Override
		public boolean equals(Object other) {
			if (this == other) {
				return true;
			}
			if (this.getClass() != other.getClass()) {
				return false;
			}
			Arc otherArc = (Arc) other;
			return this.TAIL == otherArc.TAIL && this.HEAD == otherArc.HEAD
					&& this.CONSTRAINT.equals(otherArc.CONSTRAINT);
		}

		@Override
		public int hashCode() {
			return Objects.hash(this.TAIL, this.HEAD, this.CONSTRAINT);
		}

		@Override
		public String toString() {
			return "(" + this.TAIL + " -> " + this.HEAD + ")";
		}

	}

	public class Test {
		public static void main(String args[]) {
			System.out.println();
		}
	}

}
