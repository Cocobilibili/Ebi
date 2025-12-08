use anyhow::{Result, anyhow};
use ebi_objects::{
    FiniteStochasticLanguage,
    StochasticDeterministicFiniteAutomaton,
    Activity,
    EventLog,
    HasActivityKey,
    TranslateActivityKey
};


//use std::{clone, ops::Div};
use crate::math::log_div_enum::LogDivEnum;
use std::ops::Div;
use ebi_arithmetic::{EbiMatrix, Fraction, FractionMatrix, IdentityMinus, Inversion, Signed, Zero, One};
use ebi_objects::traits::trace_iterators::IntoRefTraceProbabilityIterator;
use crate::math::log_div::LogDiv;
use ebi_arithmetic::f;

//hilffunktion: valid sdfa
pub fn is_valid_sdfa(
    sdfa: &StochasticDeterministicFiniteAutomaton,
) -> Result<()> {
    // check if sdfa is empty
    if sdfa.get_initial_state().is_none() {
        return Err(anyhow!("SDFA has no initial state"));
    }
    // check if probabilities sum to 1 for each state
    let n = sdfa.get_max_state() + 1;
    for state in 0..n {
        let mut sum = Fraction::zero();
        for (i, &src) in sdfa.get_sources().iter().enumerate() {
            if src == state {
                sum += sdfa.get_probabilities()[i].clone();
            }
        }
        sum += sdfa.get_termination_probability(state).clone();
        if !sum .is_one(){
            return Err(anyhow!(
                "Invalid probability sum at state {}: total = {} (expected 1)",
                state,
                sum
            ));
        }
    }
    for (i, p) in sdfa.get_probabilities().iter().enumerate() {
        if p.is_zero() || p.is_negative() {
            return Err(anyhow!(
                "Invalid transition probability at index {}: {} (must be > 0)",
                i,
                p
            ));
        }
    }

    // at least one terminating state
    let has_termination = (0..n)
        .any(|s| !sdfa.get_termination_probability(s).is_zero());
    if !has_termination {
        return Err(anyhow!("No terminating state found (model may livelock)"));
    }

    Ok(())
}


// hilffunktion: calculate entropy
fn entropy_calculate(p: &Fraction) -> LogDiv {
    if p.is_zero() {
        // entropy formula
        LogDiv::zero()
    } else {
        let res = LogDiv::n_log_n(p).unwrap();
        LogDiv::zero() - res
    }
}

// default lambda value
fn default_lambda() -> Fraction {
    f!(1, 10)
}

/* 
// caculate entropy of eventlog
pub fn entropy_eventlog(event_log: EventLog) -> LogDiv {
    let fsl = FiniteStochasticLanguage::from(event_log);
    let mut sum_entropy = LogDiv::zero();
    for (_, prob) in fsl.iter_traces_probabilities() {    
            sum_entropy += entropy_calculate(prob);
    }
    sum_entropy

}*/
// caculate entropy of eventlog（统一带 λ，λ=0 时退化为原公式）
pub fn entropy_eventlog(
    event_log: EventLog,
    lambda: &Fraction,
) -> LogDiv {
    let fsl = FiniteStochasticLanguage::from(event_log);

    // λ = 0
    if lambda.is_zero() {
        let mut sum_entropy = LogDiv::zero();
        for (_, prob) in fsl.iter_traces_probabilities() {
            sum_entropy += entropy_calculate(prob);
        }
        return sum_entropy;
    }

    // λ > 0：p(1-λ) and pλ
    let mut sum_entropy = LogDiv::zero();
    let one_minus = Fraction::one() - lambda.clone();

    for (_, prob) in fsl.iter_traces_probabilities() {
        // H(p(1-λ))
        let p_main = prob.clone() * one_minus.clone();
        sum_entropy += entropy_calculate(&p_main);

        // H(pλ)
        let p_tail = prob.clone() * lambda.clone();
        sum_entropy += entropy_calculate(&p_tail);
    }

    sum_entropy
}


// calculate every trace's probability in sdfa 
fn prob_of_trace_in_sdfa(
    sdfa: &StochasticDeterministicFiniteAutomaton,
    trace: &Vec<Activity>,
) -> Fraction {

    // state = None, p=0
    let mut state = match sdfa.get_initial_state() {
        Some(s) => s,
        None => return Fraction::zero(),
    };

    // init Prob = 1
    let mut p = Fraction::one();

    // calculate p
    for a in trace {
        let a_id = sdfa.activity_key().get_id_from_activity(a);
        let (found, place) = sdfa.binary_search(state, a_id);
        if !found {
            return Fraction::zero(); 
        }
        p *= sdfa.get_probabilities()[place].clone();
        state = sdfa.get_targets()[place];
    }
    // multiply the termination probability
    p * sdfa.get_termination_probability(state).clone()
    
}

//Hilfsfunktion: compare two LogDiv and return the smaller one
fn log_div_min(a: &LogDiv, b: &LogDiv) -> LogDiv {
    if a.approximate() < b.approximate() {
        a.clone()
    } else {
        b.clone()
    }
}

/* 
pub fn gain_numerator(
    event_log: EventLog,
    sdfa: &mut StochasticDeterministicFiniteAutomaton,
) -> LogDiv {
    // translate eventlog to fsl
    let mut fsl = FiniteStochasticLanguage::from(event_log);

    // make sure sdfa and fsl have the same activity_key
    {
        // get sdfa activitykey mut
        let key = sdfa.activity_key_mut();
        // sfl to sdfa
        fsl.translate_using_activity_key(key);
    }

    let mut out = LogDiv::zero();

    // FSL:  (trace, p1) 
    for (trace, p1) in fsl.iter_traces_probabilities() {
        // get trace from eventlog, and calculate the probility in sdfa
        let p2 = prob_of_trace_in_sdfa(sdfa, trace);
        // if p2 != 0, then sdfa have the trace 
        if !p2.is_zero() {
            //calculate the entropy of p1,p2
            let p_eventlog = entropy_calculate(p1);
            let p_sdfa = entropy_calculate(&p2);
            //get min(p1,p2) and sum of all entropy of traces 
            //numerator
            let min_p = log_div_min(&p_eventlog, &p_sdfa);
            out += min_p;
        }

    }
    out
}
*/


pub fn gain_numerator(
    event_log: EventLog,
    sdfa: &mut StochasticDeterministicFiniteAutomaton,
    lambda: &Fraction,
) -> LogDiv {
    // translate eventlog to fsl
    let mut fsl = FiniteStochasticLanguage::from(event_log);

    // make sure sdfa and fsl have the same activity_key
    {
        let key = sdfa.activity_key_mut();
        fsl.translate_using_activity_key(key);
    }

    let mut out = LogDiv::zero();

    // FSL:  (trace, p1)
    for (trace, p1) in fsl.iter_traces_probabilities() {
        let p2 = prob_of_trace_in_sdfa(sdfa, trace);

        // X(t)>0 and Y(t)>0
        if p2.is_zero() {
            continue;
        }

        if lambda.is_zero() {
            // λ = 0
            let p_eventlog = entropy_calculate(p1);
            let p_sdfa = entropy_calculate(&p2);
            let min_p = log_div_min(&p_eventlog, &p_sdfa);
            out += min_p;
        }else {
            // 1-λ 
            let one_minus = Fraction::one() - lambda.clone();

            // one part: X(t)(1-λ), Y(t)(1-λ)
            let p1_main = p1.clone() * one_minus.clone();
            let p2_main = p2.clone() * one_minus.clone();

            let h1 = entropy_calculate(&p1_main);
            let h2 = entropy_calculate(&p2_main);
            out += log_div_min(&h1, &h2);

            // part two：X(t)λ, Y(t)λ
            let p1_tail = p1.clone() * lambda.clone();
            let p2_tail = p2.clone() * lambda.clone();

            let h1_tail = entropy_calculate(&p1_tail);
            let h2_tail = entropy_calculate(&p2_tail);
            out += log_div_min(&h1_tail, &h2_tail);
        }
    }
    out
}



//


//c_s 
pub fn c_s(
    sdfa: &StochasticDeterministicFiniteAutomaton,
) -> Result<Vec<Fraction>> {
    let n = sdfa.get_max_state() + 1;
    let s0 = sdfa.get_initial_state().ok_or_else(|| anyhow!("no start state"))?;
    // create matrix P
    let mut p = FractionMatrix::new(n, n);
    // write probility transition to P
    for (i,&src) in sdfa.get_sources().iter().enumerate(){
        let target = sdfa.get_targets()[i];
        let prob = &sdfa.get_probabilities()[i];
        if !prob.is_zero(){
            p.increase(src, target, prob);
        }
            
    }
    // F = (I - P)^(-1)
    p.identity_minus();
    let f = p.invert()?;

    // e0（one-hot）
 
    let mut e0 = vec![Fraction::zero(); n];
    e0[s0] = Fraction::one();

    // c_s
    let c_s = (&e0 * &f)?; 
    Ok(c_s)
}

// calculate entropy of sdfa
pub fn entropy_sdfa(
    sdfa: &StochasticDeterministicFiniteAutomaton,
    lambda: &Fraction,
) -> Result<LogDiv> {
    is_valid_sdfa(sdfa)?;
    let n = sdfa.get_max_state() + 1;
    let c_s = c_s(sdfa)?;
    let mut term_entropy = LogDiv::zero();

    if lambda.is_zero() {
        let mut term_entropy = LogDiv::zero();
        for state in 0..n {
            let term_prob = sdfa.get_termination_probability(state);
            if term_prob.is_zero() {
                continue;
            }
            let mut ent = entropy_calculate(&term_prob);
            ent *= c_s[state].clone();
            term_entropy += ent;
        }

        let mut trans_entropy = LogDiv::zero();
        for (i, &src) in sdfa.get_sources().iter().enumerate() {
            let prob = &sdfa.get_probabilities()[i];
            if !prob.is_zero() {
                let mut ent = entropy_calculate(prob);
                ent *= c_s[src].clone();
                trans_entropy += ent;
            }
        }

        return Ok(trans_entropy + term_entropy);
    }

    let one_minus = Fraction::one() - lambda.clone();
    for state in 0..n {
        let term_prob = sdfa.get_termination_probability(state);
        if term_prob.is_zero() {
            continue;

        }
        //fist term : p(1-λ)
        let p_term_main = term_prob.clone() * one_minus.clone();
        //second term: add one : pλ
        let p_term_tail = term_prob.clone() * lambda.clone();

        let mut ent_main = entropy_calculate(&p_term_main);
        ent_main *= c_s[state].clone();
        term_entropy += ent_main;

        let mut ent_tail = entropy_calculate(&p_term_tail);
        ent_tail *= c_s[state].clone();
        term_entropy += ent_tail;
    }
    

    let mut one_part = LogDiv::zero();
    for (i, &src) in sdfa.get_sources().iter().enumerate() {
        let prob = &sdfa.get_probabilities()[i];
        if !prob.is_zero(){
            let mut ent = entropy_calculate(prob);
            ent *= c_s[src].clone();    
            one_part += ent;
        }
    }
    
    let entropy = one_part + term_entropy;

    Ok(entropy)

}


impl Div<LogDivEnum> for LogDivEnum {
    type Output = LogDivEnum;

    fn div(mut self, rhs: LogDivEnum) -> LogDivEnum {
        self -= rhs; 
        self
    }
}


// Computes Potential Gain Precision:
// P = GainNumerator(L, A) / H(L)
// where H(L) is the entropy of the event log.
pub fn potential_gain_precision(
    event_log: EventLog,
    sdfa: &StochasticDeterministicFiniteAutomaton,
    lambda: &Fraction,
) -> Result<LogDiv> {
    is_valid_sdfa(sdfa)?;
    let mut sdfa_cloned = sdfa.clone();
    let num = gain_numerator(event_log.clone(), &mut sdfa_cloned, lambda);
    let denom = entropy_eventlog(event_log.clone(), lambda);
    if denom.is_zero() {
        return Err(anyhow!("Denominator (entropy of event log) is zero"));
    }
    Ok(num / denom)
}

// Computes Potential Gain Recall:
// P = GainNumerator(L, A) / H(A)
// where H(A) is the entropy of the SDFA model.
pub fn potential_gain_recall(
    event_log: EventLog, 
    sdfa: &StochasticDeterministicFiniteAutomaton,
    lambda: &Fraction,
) -> Result<LogDiv> {
    // Clone sdfa because entropy_sdfa expects a mutable reference
    is_valid_sdfa(sdfa)?;
    let mut sdfa_cloned = sdfa.clone();
    let num =  gain_numerator(event_log.clone(), &mut sdfa_cloned, lambda);
    let denom = entropy_sdfa(&sdfa_cloned, lambda)?;
    if denom.is_zero() {
        return Err(anyhow!("Denominator (entropy of SDFA) is zero"));
    }
    let entropy = num / denom;
    Ok(entropy)
}

///  λ = 1e-6 precision
pub fn potential_gain_precision_default(
    event_log: EventLog,
    sdfa: &StochasticDeterministicFiniteAutomaton,
) -> Result<LogDiv> {
    let lambda = default_lambda(); // 1e-6
    potential_gain_precision(event_log, sdfa, &lambda)
}

///  λ = 1e-6  recall
pub fn potential_gain_recall_default(
    event_log: EventLog,
    sdfa: &StochasticDeterministicFiniteAutomaton,
) -> Result<LogDiv> {
    let lambda = default_lambda(); // 1e-6
    potential_gain_recall(event_log, sdfa, &lambda)
}



#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::log_div::LogDiv;
    use ebi_arithmetic::f;
    use ebi_objects::StochasticDeterministicFiniteAutomaton;
    use anyhow::Result;
    //creat 2 xes files
    fn xes_l1() -> &'static str {
        //1. []*2 + [a]*8
        //entropy = - (2/10 * log2(2/10) + 8/10 * log2(8/10)) = 0.7219280948874
        r#"<?xml version="1.0" encoding="UTF-8" ?>
        <log xmlns="http://www.xes-standard.org/">
            <!-- [] ×2 -->
            <trace></trace>
            <trace></trace>
            <!-- [a] ×8 -->
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
            <trace><event><string key="concept:name" value="a"/></event></trace>
        </log>"#
    }

    fn xes_l2() -> &'static str {
    //2. []*1 + [a]*2 + [a,a]*1 + [a,a,a]*6
    //entropy = - (1/10 * log2(1/10) + 2/10 * log2(2/10) + 1/10 * log2(1/10) + 6/10 * log2(6/10)) = 1.5709505944547
 
        r#"<?xml version="1.0" encoding="UTF-8" ?>
        <log xmlns="http://www.xes-standard.org/">
        <!-- [] ×1 -->
        <trace></trace>

        <!-- [a] ×2 -->
        <trace><event><string key="concept:name" value="a"/></event></trace>
        <trace><event><string key="concept:name" value="a"/></event></trace>

        <!-- [a,a] ×1 -->
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>

        <!-- [a,a,a] ×6 -->
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>
        <trace>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
            <event><string key="concept:name" value="a"/></event>
        </trace>
        </log>"#
    }


    

    

    


    #[test]
        //test entropy_eventlog
    fn test_entropy_eventlog(){
         let lambda0 = Fraction::zero();
        //xes -> eventlog
        let event1: EventLog = xes_l1().parse().unwrap();
        let event2: EventLog = xes_l2().parse().unwrap();

        let entropy1 = entropy_eventlog(event1.clone(), &lambda0);
        let entropy2= entropy_eventlog(event2.clone(), &lambda0);

        //- (2/10 * log2(2/10) + 8/10 * log2(8/10))
        let x = 
        LogDiv::n_log_n(&f!(2,10)).unwrap();
        let y =
        LogDiv::n_log_n(&f!(8,10)).unwrap();
        
        let _x_print = x.clone();
        let _y_print = y.clone();
        let expected1 = (LogDiv::zero() - x) + (LogDiv::zero() - y);
        
        
        //- (1/10 * log2(1/10) + 2/10 * log2(2/10) + 1/10 * log2(1/10) + 6/10 * log2(6/10))
        let a = LogDiv::n_log_n(&f!(1,10)).unwrap();
        let b = LogDiv::n_log_n(&f!(2,10)).unwrap();
        let c = LogDiv::n_log_n(&f!(1,10)).unwrap();
        let d = LogDiv::n_log_n(&f!(6,10)).unwrap();
        let _a_print = a.clone();
        let _b_print = b.clone();
        let _c_print = c.clone();
        let _d_print = d.clone();
        let expected2 = LogDiv::zero() - (a + b + c + d);

        assert_eq!(entropy1, expected1);
        assert_eq!(entropy2, expected2);
        
    }

    #[test]
    //test gain_numerator
    fn test_gain_numerator(){
         let lambda0 = Fraction::zero();
        //xes -> eventlog
        let event1: EventLog = xes_l1().parse().unwrap();
        let event2: EventLog = xes_l2().parse().unwrap();

        //creat a sdfa
        let sdfa: StochasticDeterministicFiniteAutomaton = event1.clone().into();
        let gain1= gain_numerator(event1.clone(), &mut sdfa.clone(), &lambda0);
        let _gain2= gain_numerator(event2.clone(), &mut sdfa.clone(), &lambda0);


        // case 1: gain_numerator(event1, sdfa_from_event1) == entropy(event1)
        let entropy1 = entropy_eventlog(event1.clone(), &lambda0);
        assert_eq!(entropy1, gain1);

        //case 2: gain(event2, sdfa_from_event1) = 0.5897352854
        let g1= LogDiv::zero() - LogDiv::n_log_n(&f!(2,10)).unwrap();
        let g2 = LogDiv::zero() - LogDiv::n_log_n(&f!(1,10)).unwrap();
        let gain_num1 = log_div_min(&g1, &g2);

        let _a1 =LogDiv::zero() - LogDiv::n_log_n(&f!(8,10)).unwrap();
        let _a2 =LogDiv::zero() - LogDiv::n_log_n(&f!(2,10)).unwrap();
        //let _a_print = _a1.clone();
        //let _b_print = _a2.clone();
        let gain_num2 = log_div_min(&_a1, &_a2);

        let gain_num = gain_num1 + gain_num2;

        assert_eq!(_gain2, gain_num);
    }

    fn event_log_to_sdfa(
        log: &EventLog,
        ) -> StochasticDeterministicFiniteAutomaton {
            Into::<StochasticDeterministicFiniteAutomaton>::into(log.clone())
    }
    #[test]
    fn test_entropy_sdfa()  -> Result<()> {
        /*//creste a sdfa
        let mut sdfa = StochasticDeterministicFiniteAutomaton::new();

        // inital state s0
        sdfa.set_initial_state(Some(0));
        let a = sdfa.activity_key.process_activity("a");

        // transition s0 --a(0.8)--> s1
        sdfa.add_transition(0, a.clone(), 1, f!(8, 10))?;

        // transition s1 --a(0.5)--> s1
        sdfa.add_transition(1, a, 1, f!(5, 10))?;

    
        //calculate c_s
        let c_s = c_s(&sdfa)?;
        //println!("c_s = {:?}", c_s);
        let expected = vec![f!(1,1), f!(8,5)];
        assert_eq!(c_s, expected);

        //calculate entropy_sdfa
        //one_part = - (1/2 * log2(1/2) * 1 + 8/10 * log2(8/10) * 8/5)
        let mut a = LogDiv::n_log_n(&f!(8,10))?; 
        a*= f!(1,1);     
        let a_sdfa = LogDiv::zero() - a;

        let mut b = LogDiv::n_log_n(&f!(1,2))?;
        b*= f!(8,5);
        let b_sdfa = LogDiv::zero() - b;

        let one_part = a_sdfa + b_sdfa;
        println!("one_part = {:?}", one_part);

        //term_part = - (1/2 * log2(1/2) * 8/5 + 2/10 * log2(2/10) * 1)
        let mut term_s0 = LogDiv::n_log_n(&f!(2,10))?;
        term_s0 *= f!(1,1);
        let term_s0_ = LogDiv::zero() - term_s0;
        let mut term_s1 = LogDiv::n_log_n(&f!(1,2))?;
        term_s1 *= f!(8,5);
        let term_s1_ = LogDiv::zero() - term_s1;
        let term     = term_s0_ + term_s1_;
        println!("term = {:?}", term);

        let e_sdfa   = one_part + term;
        let entropy_sdfa = entropy_sdfa(&sdfa)?;
        
  

        assert_eq!(entropy_sdfa.approximate(), e_sdfa.approximate());
        Ok(())*/


        // XES -> EventLog
        let event1: EventLog = xes_l1().parse()?;  

        // EventLog -> SDFA
        let sdfa1 = event_log_to_sdfa(&event1);

        // λ = 0
        let lambda0 = Fraction::zero();

        // Calculate entropy_sdfa with λ = 0
        let h1: LogDiv = entropy_sdfa(&sdfa1, &lambda0)?;

        let entropy1 = entropy_eventlog(event1.clone(), &lambda0);
        println!("eventlog entropy ≈ {:.12} bits", entropy1.approximate());
        assert_eq!(h1.approximate(), entropy1.approximate());

        Ok(())

    }

    #[test]
    fn test_entropy_eventlog_with_lambda() {
        let lambda0 = Fraction::zero();
        let lambda = default_lambda(); // 1e-6

        let event1: EventLog = xes_l1().parse().unwrap();

        let h0 = entropy_eventlog(event1.clone(), &lambda0);
        let h_lambda = entropy_eventlog(event1.clone(), &lambda);

        println!("H(L, λ=0)      ≈ {:.12}", h0.approximate());
        println!("H(L, λ=1e-6)   ≈ {:.12}", h_lambda.approximate());

        let a = h_lambda.approximate();
        let b = h0.approximate();
        assert!(
            a >= b,
            "H(L, λ) = {:?} < H(L, 0) = {:?}",
            a,
            b
        );
    }

    #[test]
    fn test_entropy_sdfa_with_lambda() -> Result<()> {
        let event1: EventLog = xes_l1().parse()?;  
        let sdfa1 = event_log_to_sdfa(&event1);

        let lambda0 = Fraction::zero();
        let lambda = default_lambda(); // 1e-6

        let h0: LogDiv = entropy_sdfa(&sdfa1, &lambda0)?;
        let h_lambda: LogDiv = entropy_sdfa(&sdfa1, &lambda)?;

        println!("H(A, λ=0)    ≈ {:.12}", h0.approximate());
        println!("H(A, λ=1e-6) ≈ {:.12}", h_lambda.approximate());

    // 直接在 FractionEnum 上比较：H(A, λ) >= H(A, 0)
        let a = h_lambda.approximate();
        let b = h0.approximate();
        assert!(
            a >= b,
            "H(A, λ) = {:?} < H(A, 0) = {:?}",
            a,
            b
        );

        Ok(())
    }
/* 
    #[test]
    fn test_potential_gain_default_lambda_smoke() -> Result<()> {
        let event1: EventLog = xes_l1().parse()?;
        let sdfa: StochasticDeterministicFiniteAutomaton = event1.clone().into();

        let p = potential_gain_precision_default(event1.clone(), &sdfa)?;
        let r = potential_gain_recall_default(event1.clone(), &sdfa)?;

        println!("P_default(λ=1e-6) ≈ {:.12}", p.approximate());
        println!("R_default(λ=1e-6) ≈ {:.12}", r.approximate());

        // 不做严格数值断言，只要是正常有限值即可
        assert!(p.approximate().is_finite());
        assert!(r.approximate().is_finite());

        Ok(())
    }*/


}

