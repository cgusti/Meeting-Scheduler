package main.csp;

import java.time.LocalDate;
import java.util.Arrays;
import java.util.Set;
import java.util.HashSet;

/**
 * DateConstraint superclass: all date constraints will have
 * an L_VAL variable and some operation that compares it to
 * some other variable or date value.
 */
public abstract class DateConstraint {

    public final int L_VAL;
    public final String OP;
    public final int ARITY;
    
    private static final Set<String> LEGAL_OPS = new HashSet<>(
        Arrays.asList("==", "!=", "<", "<=", ">", ">=")
    );
    
    /**
     * Constructs a new DateConstraint object with the given lVal,
     * operator, and arity.
     * @param lVal The index of the meeting variable corresponding to this constraint. what is meeting variable? 
     * @param operator The comparator from amongst those in LEGAL_OPS
     * @param arity The arity of the constraint (1 for unary, 2 for binary)
     */
    
    public DateConstraint (int lVal, String operator, int arity) {
        if (!LEGAL_OPS.contains(operator)) {
            throw new IllegalArgumentException("Invalid constraint operator");
        }
        if (lVal < 0) {
            throw new IllegalArgumentException("Invalid variable index");
        }
        
        this.L_VAL = lVal;
        this.OP = operator;
        this.ARITY = arity;
    }
    
    /**
     * Returns whether or not the given constraint is satisfied with the given LValue, constraint, and RValue
     * such that LValue constraint.OP RValue is true or not
     * @param leftDate The LValue to compare in the constraint
     * @param rightDate The RValue to compare in the constraint
     * @return Whether or not the constraint is satisfied with the given dates.
     */
    public boolean isSatisfiedBy (LocalDate leftDate, LocalDate rightDate) {
        switch (this.OP) {
        case "==": return leftDate.isEqual(rightDate);
        case "!=": return !leftDate.isEqual(rightDate);
        case ">":  return leftDate.isAfter(rightDate);
        case "<":  return leftDate.isBefore(rightDate);
        case ">=": return leftDate.isAfter(rightDate) || leftDate.isEqual(rightDate);
        case "<=": return leftDate.isBefore(rightDate) || leftDate.isEqual(rightDate);
        }
        return false;
    }
    
    /**
     * Returns the symmetrical operator of this constraint if the LValue and RValue were swapped.
     * Useful for arc-consistency algorithm.
     * @return The operator symmetrical to this constraint's.
     */
    public String getSymmetricalOp () {
        switch (this.OP) {
        case ">":  return "<";
        case "<":  return ">";
        case ">=": return "<=";
        case "<=": return ">=";
        default:   return this.OP;
        }
    }
    
    /**
     * The arity of a constraint determines the number of variables
     * found within
     * @return 1 for UnaryDateConstraints, 2 for Binary
     */
    public int arity () {
        return this.ARITY;
    }
    
    @Override
    public String toString () {
        return L_VAL + " " + OP;
    }
    
}
