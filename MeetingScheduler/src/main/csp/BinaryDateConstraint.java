package main.csp;

import java.util.Objects;

/**
 * BinaryDateConstraints are those in which two variables
 * are being compared by some operator, specified by an
 * int L_VAL and R_VAL for the corresponding variable / meeting
 * indexes, such as:
 * 0 == 1
 *   OR
 * 3 <= 5
 */
public class BinaryDateConstraint extends DateConstraint {

    public final int R_VAL;
    
    /**Constructor 
     * Constructs a new BinaryDateConstraint relating two Meeting Variable indexes
     * of the format:
     *     lVal op rVal
     * Ex: 0 == 1 
     * @param lVal The left meeting index
     * @param operator The comparator
     * @param rVal The right meeting index
     */
    public BinaryDateConstraint (int lVal, String operator, int rVal) {
        super(lVal, operator, 2);
        if (rVal < 0 || lVal == rVal) {
            throw new IllegalArgumentException("Invalid variable index");
        }
        
        this.R_VAL = rVal;
    }
    
    /**
     * Returns a new BinaryDateConstraint that is equivalent to this one, but with
     * lVal and rVal swapped. Ex:
     * 0 < 1 becomes 1 > 0
     * @return A new, equivalent BinaryDateConstraint with swapped lVal and rVal.
     */
    public BinaryDateConstraint getReverse () {
        return new BinaryDateConstraint(this.R_VAL, this.getSymmetricalOp(), this.L_VAL);
    }
    
    
    @Override
    public boolean equals (Object other) {
        if (this == other) { return true; }
        if (this.getClass() != other.getClass()) { return false; }
        BinaryDateConstraint otherDC = (BinaryDateConstraint) other;
        BinaryDateConstraint reversed = this.getReverse();
        return (this.L_VAL == otherDC.L_VAL && this.OP.equals(otherDC.OP) && this.R_VAL == otherDC.R_VAL) ||
               (reversed.R_VAL == otherDC.L_VAL && reversed.OP.equals(otherDC.OP) && reversed.L_VAL == otherDC.R_VAL);
    }
    
    @Override
    public int hashCode () {
        return Objects.hash(this.L_VAL, this.OP, this.R_VAL);
    }
    
    @Override
    public String toString () {
        return super.toString() + " " + this.R_VAL;
    }
    
}
