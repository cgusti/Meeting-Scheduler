package main.csp;

import java.time.LocalDate;

/**
 * UnaryDateConstraints are those in which one variable
 * is being compared by some operator, specified by an
 * int L_VAL (for the corresponding variable 
 * / meeting index) and LocalDate R_VAL, such as:
 * 0 == 2019-1-3
 *   OR
 * 3 <= 2019-11-9
 */
public class UnaryDateConstraint extends DateConstraint {

    public final LocalDate R_VAL;
    
    /**
     * Constructs a new UnaryDateConstraint relating a meeting variable index in the
     * L_VAL to a date in the R_VAL:
     *     lVal op rVal
     * Ex: 0 == LocalDate.of(2022, 1, 1)
     * @param lVal The meeting index
     * @param operator The comparator
     * @param rVal A date
     */
    public UnaryDateConstraint (int lVal, String operator, LocalDate rVal) {
        super(lVal, operator, 1);
        this.R_VAL = rVal;
    }
    
    @Override
    public String toString () {
        return super.toString() + " " + this.R_VAL;
    }
    
}
