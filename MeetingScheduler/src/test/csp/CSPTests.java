package test.csp;

import static org.junit.Assert.*;

import org.junit.AfterClass;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestWatcher;
import org.junit.rules.Timeout;
import org.junit.runner.Description;

import java.time.LocalDate;
import java.util.*;
import main.csp.*;
import static main.csp.CSPSolver.*;

public class CSPTests {
    
    // =================================================
    // Test Configuration
    // =================================================
    
    // Global timeout to prevent infinite loops from
    // crashing the test suite + to test that your
    // constraint propagation is working...
    @Rule
    public Timeout globalTimeout = Timeout.seconds(2000);
    
    // Grade record-keeping
    static int possible = 0, passed = 0;
    
    // the @Before method is run before every @Test
    @Before
    public void init () {
        possible++;
    }
    
    // Each time you pass a test, you get a point! Yay!
    // [!] Requires JUnit 4+ to run
    @Rule
    public TestWatcher watchman = new TestWatcher() {
        @Override
        protected void succeeded(Description description) {
            passed++;
        }
    };
    
    // Used for grading, reports the total number of tests
    // passed over the total possible
    @AfterClass
    public static void gradeReport () {
        System.out.println("============================");
        System.out.println("Tests Complete");
        System.out.println(passed + " / " + possible + " passed!");
        if ((1.0 * passed / possible) >= 0.9) {
            System.out.println("[!] Nice job!"); // Automated acclaim!
        }
        System.out.println("============================");
    }
    
    /**
     * Tests whether a given solution to a CSP satisfies all constraints or not
     * @param soln Full instantiation of variables to assigned values, indexed by variable
     * @param constraints The set of constraints the solution must satisfy
     */
    public static void testSolution (List<LocalDate> soln, Set<DateConstraint> constraints) {
        for (DateConstraint d : constraints) {
            LocalDate leftDate = soln.get(d.L_VAL),
                      rightDate = (d.arity() == 1) 
                          ? ((UnaryDateConstraint) d).R_VAL 
                          : soln.get(((BinaryDateConstraint) d).R_VAL);
            
            if (!d.isSatisfiedBy(leftDate, rightDate)) {
                fail("[X] Constraint Failed: " + d);
            }
        }
    }
    
    /**
     * Helper method for generating uniform domains for tests.
     * @param n Number of meeting variables in this CSP.
     * @param startRange Start date for the range of each variable's domain.
     * @param endRange End date for the range of each variable's domain.
     * @return The List of Meeting-indexed MeetingDomains.
     */
    public static List<MeetingDomain> generateDomains (int n, LocalDate startRange, LocalDate endRange) {
        List<MeetingDomain> domains = new ArrayList<>();
        while (n > 0) {
            domains.add(new MeetingDomain(startRange, endRange));
            n--;
        }
        return domains;
    }
    
    
    // =================================================
    // Unit Tests
    // =================================================
    
    // Filtering Tests
    // -------------------------------------------------
    
    @Test
    public void filtering_t0() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "==", LocalDate.of(2022, 1, 3))
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        // One Meeting with possible values ranging from 2022-1-1 to 2022-1-5
        List<MeetingDomain> domains = generateDomains(1, startRange, endRange);
        
        
        nodeConsistency(domains, constraints);
        
       
        assertEquals(1, domains.get(0).domainValues.size());
        assertTrue(domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 3)));
    }
   
    @Test
    public void filtering_t1() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "<", LocalDate.of(2022, 1, 3))
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        List<MeetingDomain> domains = generateDomains(1, startRange, endRange);
        
        nodeConsistency(domains, constraints);
        
        assertEquals(2, domains.get(0).domainValues.size());
        assertTrue(domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 1)));
        assertTrue(domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 2)));
    }


    @Test
    public void filtering_t2() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "!=", LocalDate.of(2022, 1, 3)),
                new UnaryDateConstraint(1, "<", LocalDate.of(2022, 1, 2))
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        List<MeetingDomain> domains = generateDomains(3, startRange, endRange);
        
        nodeConsistency(domains, constraints);
        
        assertEquals(4, domains.get(0).domainValues.size());
        assertTrue(!domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 3)));
        assertEquals(1, domains.get(1).domainValues.size());
        assertTrue(domains.get(1).domainValues.contains(LocalDate.of(2022, 1, 1)));
        assertEquals(5, domains.get(2).domainValues.size());
    }
    

    @Test
    public void filtering_t3() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "!=", 1)
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        List<MeetingDomain> domains = generateDomains(2, startRange, endRange);
        
        nodeConsistency(domains, constraints);
        
        assertEquals(5, domains.get(0).domainValues.size());
        assertEquals(5, domains.get(1).domainValues.size());
    }
    
  
    @Test
    public void filtering_t4() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "<", 1)
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        List<MeetingDomain> domains = generateDomains(2, startRange, endRange);
        
        arcConsistency(domains, constraints);
        
        assertEquals(4, domains.get(0).domainValues.size());
        assertTrue(!domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 5)));
        assertEquals(4, domains.get(1).domainValues.size());
        assertTrue(!domains.get(1).domainValues.contains(LocalDate.of(2022, 1, 1)));
    }
    

    @Test
    public void filtering_t5() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "<", 1),
                new BinaryDateConstraint(1, "<", 0)
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        List<MeetingDomain> domains = generateDomains(2, startRange, endRange);
        
        arcConsistency(domains, constraints);
        
        assertEquals(0, domains.get(0).domainValues.size());
        assertEquals(0, domains.get(1).domainValues.size());
    }
   
    @Test
    public void filtering_t6() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "<", 1),
                new BinaryDateConstraint(1, "<", 2),
                new BinaryDateConstraint(2, "<", 0)
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        // One Meeting with possible values ranging from 2022-1-1 to 2022-1-5
        List<MeetingDomain> domains = generateDomains(3, startRange, endRange);
        
        arcConsistency(domains, constraints);
        
        assertEquals(0, domains.get(0).domainValues.size());
        assertEquals(0, domains.get(1).domainValues.size());
        assertEquals(0, domains.get(2).domainValues.size());
    }
 
    @Test
    public void filtering_t7() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "==", 1),
                new BinaryDateConstraint(1, "!=", 2),
                new BinaryDateConstraint(2, "<", 0)
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 2);
        
        // One Meeting with possible values ranging from 2022-1-1 to 2022-1-5
        List<MeetingDomain> domains = generateDomains(3, startRange, endRange);
        
        arcConsistency(domains, constraints);
        
        assertEquals(1, domains.get(0).domainValues.size());
        assertTrue(domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 2)));
        assertEquals(1, domains.get(1).domainValues.size());
        assertTrue(domains.get(1).domainValues.contains(LocalDate.of(2022, 1, 2)));
        assertEquals(1, domains.get(2).domainValues.size());
        assertTrue(domains.get(2).domainValues.contains(LocalDate.of(2022, 1, 1)));
    }
    
    @Test
    public void filtering_t8() {
       Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "==", 1),
                new BinaryDateConstraint(1, "==", 2),
                new UnaryDateConstraint(2, "==", LocalDate.of(2022, 1, 1))
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 2);
        
        // One Meeting with possible values ranging from 2022-1-1 to 2022-1-5
        List<MeetingDomain> domains = generateDomains(3, startRange, endRange);
        
        nodeConsistency(domains, constraints);
        arcConsistency(domains, constraints);
        
        assertEquals(1, domains.get(0).domainValues.size());
        assertTrue(domains.get(0).domainValues.contains(LocalDate.of(2022, 1, 1)));
        assertEquals(1, domains.get(1).domainValues.size());
        assertTrue(domains.get(1).domainValues.contains(LocalDate.of(2022, 1, 1)));
        assertEquals(1, domains.get(2).domainValues.size());
        assertTrue(domains.get(2).domainValues.contains(LocalDate.of(2022, 1, 1)));
    }
   
    @Test
    public void filtering_t9() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(1, "!=", 0),
                new BinaryDateConstraint(1, "<", 2),
                new UnaryDateConstraint(2, "<=", LocalDate.of(2022, 1, 3)),
                new UnaryDateConstraint(0, ">=", LocalDate.of(2022, 1, 3))
            )
        );
        
        LocalDate startRange = LocalDate.of(2022, 1, 1),
                  endRange   = LocalDate.of(2022, 1, 5);
        
        // One Meeting with possible values ranging from 2022-1-1 to 2022-1-5
        List<MeetingDomain> domains = generateDomains(3, startRange, endRange);
        
        nodeConsistency(domains, constraints);
        arcConsistency(domains, constraints);
        
        assertEquals(3, domains.get(0).domainValues.size());
        assertEquals(2, domains.get(1).domainValues.size());
        assertEquals(2, domains.get(2).domainValues.size());
    }
    
    
//    // CSPSolver Tests
//    // -------------------------------------------------
    @Test
    public void solve_t0() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "==", LocalDate.of(2022, 1, 3))
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-5 in which the only meeting date
        // for 1 meeting can be on 2022-1-3
        List<LocalDate> solution = solve(
            1,                          // Number of meetings to schedule
            LocalDate.of(2022, 1, 1),   // Domain start date
            LocalDate.of(2022, 1, 5),   // Domain end date
            constraints                 // Constraints all meetings must satisfy
        );
        
        // Example Solution:
        // [2022-01-03]
        testSolution(solution, constraints);
    }
  
    @Test
    public void solve_t1() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "==", LocalDate.of(2022, 1, 6))
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-5 in which the only meeting date
        // for 1 meeting can be on 2022-1-6, which is outside of the allowable
        // range, so no solution here!
        List<LocalDate> solution = solve(
            1,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 5),
            constraints
        );
        
        assertNull(solution);
    }

    @Test
    public void solve_t2() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, ">", LocalDate.of(2022, 1, 3))
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-5 in which the only meeting date
        // for 1 meeting can be AFTER 2022-1-3
        List<LocalDate> solution = solve(
            1,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 5),
            constraints
        );
        
        // Example Solution:
        // [2022-01-05]
        testSolution(solution, constraints);
    }
    
    
    @Test
    public void solve_t3() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, ">", LocalDate.of(2022, 1, 3)),
                new UnaryDateConstraint(1, ">", LocalDate.of(2022, 1, 3))
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-5 in which the only meeting date
        // for 2 meetings can be AFTER 2022-1-3 (nothing here saying that they
        // can't be on the same day!)
        List<LocalDate> solution = solve(
            2,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 5),
            constraints
        );
        
        // Example Solution:
        // [2022-01-05, 2022-01-05]
        testSolution(solution, constraints);
    }

    
    @Test
    public void solve_t4() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, "<=", LocalDate.of(2022, 1, 2)),
                new UnaryDateConstraint(1, "<=", LocalDate.of(2022, 1, 2)),
                new BinaryDateConstraint(0, "!=", 1)
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-5 in which the only meeting date
        // for 2 meetings can be BEFORE or ON 2022-1-2 but NOW they can't be on the
        // same date!
        List<LocalDate> solution = solve(
            2,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 5),
            constraints
        );
        
        // Example Solution:
        // [2022-01-02, 2022-01-01]
        testSolution(solution, constraints);
    }
    
    @Test
    public void solve_t5() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "!=", 1),
                new BinaryDateConstraint(0, "!=", 2),
                new BinaryDateConstraint(1, "!=", 2)
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-2 in which the only meeting date
        // for 3 meetings in a narrow time window that can't have the same
        // date! (impossible)
        List<LocalDate> solution = solve(
            3,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 2),
            constraints
        );
        
        assertNull(solution);
    }
    
    @Test
    public void solve_t6() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "!=", 1),
                new BinaryDateConstraint(0, "!=", 2),
                new BinaryDateConstraint(1, "!=", 2)
            )
        );
        
        // Date range of 2022-1-1 to 2022-1-2 in which the only meeting date
        // for 3 meetings in a less narrow time window that can't have the same
        // date! (impossible)
        List<LocalDate> solution = solve(
            3,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 3),
            constraints
        );
        
        // Example Solution:
        // [2022-01-03, 2022-01-02, 2022-01-01]
        testSolution(solution, constraints);
    }
    
    @Test
    public void solve_t7() {

    	Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new BinaryDateConstraint(0, "!=", 1),
                new BinaryDateConstraint(1, "==", 2),
                new BinaryDateConstraint(2, "!=", 3),
                new BinaryDateConstraint(3, "==", 4),
                new BinaryDateConstraint(4, "<", 0),
                new BinaryDateConstraint(3, ">", 2)
            )
        );
        
        // Here's a puzzle for you...
        List<LocalDate> solution = solve(
            5,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 1, 3),
            constraints
        );
        
        // Example Solution:
        // [2022-01-03, 2022-01-01, 2022-01-01, 2022-01-02, 2022-01-02]
        testSolution(solution, constraints);
    }
  
    @Test
    public void solve_t8() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, ">", LocalDate.of(2022, 1, 1)),
                new UnaryDateConstraint(1, ">", LocalDate.of(2022, 2, 1)),
                new UnaryDateConstraint(2, ">", LocalDate.of(2022, 3, 1)),
                new UnaryDateConstraint(3, ">", LocalDate.of(2022, 4, 1)),
                new UnaryDateConstraint(4, ">", LocalDate.of(2022, 5, 1)),
                new BinaryDateConstraint(0, ">", 4),
                new BinaryDateConstraint(1, ">", 3),
                new BinaryDateConstraint(2, "!=", 3),
                new BinaryDateConstraint(4, "!=", 0),
                new BinaryDateConstraint(3, ">", 2)
            )
        );
        
        // This one's simple, but requires some NODE consistency
        // preprocessing to solve in a tractable amount of time
        List<LocalDate> solution = solve(
            5,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 5, 15),
            constraints
        );
        
        // Example Solution:
        // [2022-05-15, 2022-05-15, 2022-04-30, 2022-05-14, 2022-05-14]
        testSolution(solution, constraints);
    }
 
    @Test
    public void solve_t9() {
        Set<DateConstraint> constraints = new HashSet<>(
            Arrays.asList(
                new UnaryDateConstraint(0, ">", LocalDate.of(2022, 1, 1)),
                new UnaryDateConstraint(1, ">", LocalDate.of(2022, 2, 1)),
                new UnaryDateConstraint(2, ">", LocalDate.of(2022, 3, 1)),
                new UnaryDateConstraint(3, ">", LocalDate.of(2022, 4, 1)),
                new UnaryDateConstraint(4, ">", LocalDate.of(2022, 5, 1)),
                new BinaryDateConstraint(0, ">", 4),
                new BinaryDateConstraint(1, ">", 3),
                new BinaryDateConstraint(2, "!=", 3),
                new BinaryDateConstraint(4, "!=", 0),
                new BinaryDateConstraint(3, ">", 2)
            )
        );
        
        // This one's simple, but requires some NODE + ARC consistency
        // preprocessing to solve in a tractable amount of time
        List<LocalDate> solution = solve(
            5,
            LocalDate.of(2022, 1, 1),
            LocalDate.of(2022, 6, 30),
            constraints
        );
        
        // Example Solution:
        // [2022-05-31, 2022-04-30, 2022-04-28, 2022-04-29, 2022-05-30]
        testSolution(solution, constraints);
    }
    
}
