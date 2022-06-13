package main.csp;

import java.time.LocalDate;
import java.util.*;

/**
 * Helper class used to manage Meeting Variable domains in both the
 * Backtracking scheduler and the Filtering methods of the CSP solver.
 */
public class MeetingDomain {
    
    public Set<LocalDate> domainValues;
    
    /**
     * Creates a new MeetingDomain with all dates between the given rangeStart
     * and rangeEnd (inclusive).
     * @param rangeStart The beginning date of the domain.
     * @param rangeEnd The end date of the domain.
     */
    public MeetingDomain (LocalDate rangeStart, LocalDate rangeEnd) {
        this.domainValues = new HashSet<>();
        for (LocalDate date = rangeStart; date.isBefore(rangeEnd) || date.isEqual(rangeEnd); date = date.plusDays(1)) {
            this.domainValues.add(date);
        }
    }
    
    /**
     * Copy-constructor for a MeetingDomain that initializes it with the
     * same values as the other.
     * @param other Other MeetingDomain from which to make a copy.
     */
    
    
    public MeetingDomain (MeetingDomain other) {
        this.domainValues = new HashSet<>(other.domainValues);
    }
    
    @Override
    public String toString () {
        return this.domainValues.toString();
    }

}
