
restart;
unprotect(D)
;


# ===============================================================
# Lemmas 
# ===============================================================

# ---------------------------------------------------------------
# Lemma 2.6 
# ---------------------------------------------------------------

Lemma2_6 := proc(dF, dG, hF, hG, s) 
 local h_DeltaFG; 

 h_DeltaFG := (dF + dG)*ln(dF + dG) + dF*(hG + s*dG) + 
dG*(hF + dF*s) + 2*ln(s + 1)*dF*dG;

 h_DeltaFG := s*h_DeltaFG + 2*hF + hG; 

 return h_DeltaFG; 
end proc:

Lemma2_6(dF, dG, hF, hG, s)
;

# ---------------------------------------------------------------
# Lemma 4.3 
# ---------------------------------------------------------------
Lemma4_3 := proc(n, r, D1, D2, H1, H2) 
 local s, dF, dG, hF, hG, h_Delta_union, h_Delta_union0, h_Delta_union1, h_Delta_union2; 
 s := (n + 1)*r; 
 dF := (r + 1)*(D1 + D2); # degree of P = CV1CV2
 dG := (r + 1)*(D1 + D2); # degree of partialP partial U00 = CV1CV2
 hF := H1 + H2 + (r + 1)*ln(n + 2)*(D1 + D2); # height of P = CV1CV2
 hG := H1 + H2 + (r + 1)*ln(n + 2)*(D1 + D2) + ln(D1 + D2); # height of partialP partial U00 = CV1CV2

 h_Delta_union0 := Lemma2_6(dF, dG, hF, hG, s);

 h_Delta_union1 := Lemma2_6((r+1)*D1, (r+1)*D1, H1 + (r+1)*ln(n+2)*D1, H1 + (r+1)*ln(n+2)*D1 + ln(D1), s);
 h_Delta_union2 := Lemma2_6((r+1)*D2, (r+1)*D2, H1 + (r+1)*ln(n+2)*D2, H2 + (r+1)*ln(n+2)*D2 + ln(D2), s);

 h_Delta_union := h_Delta_union0 + h_Delta_union1 + h_Delta_union2;

 h_Delta_union := expand(h_Delta_union);
 h_Delta_union := simplify(h_Delta_union);

 return h_Delta_union; 
end proc:

expr := Lemma4_3(n, r, D1, D2, H1, H2)
;

# ---------------------------------------------------------------
# Lemma 4.7
# ---------------------------------------------------------------
Lemma4_7 := proc(H, r, D, n) 
 local s, Hprime, h_Generic_Projection_Chow_CV, H_infinity_f_i, deg_g, h_infinity, d; 
 Hprime := H + (r + 1)*D*ln(n + 2); 
 s := (r + 1)*(n + 1); 
 H_infinity_f_i := Hprime; deg_g := ((r + 1)*D); h_infinity := 0; d:= 1;
 
 h_Generic_Projection_Chow_CV := H_infinity_f_i + deg_g*(h_infinity + ln(s + 1) + ln(2*n + 2)*d); 

 h_Generic_Projection_Chow_CV := expand(h_Generic_Projection_Chow_CV);
 h_Generic_Projection_Chow_CV := simplify(h_Generic_Projection_Chow_CV);
 return h_Generic_Projection_Chow_CV; 
end proc:

Lemma4_7(H, r, D, n)
;

# ---------------------------------------------------------------
# Lemma 4.9
# ---------------------------------------------------------------

Lemma4_9 := proc(n, r, d, D, h, H) 
 local h_Delta_V_G_sep_H, h_Delta0, h_Delta1, h_Delta2, Hprime, Hprime_prime, dF, hF, dG, hG, s; 
 Hprime := H + (r + 1)*D*ln(n + 2); 
 Hprime_prime := Hprime + r*D + ln(D); 

 # Delta0
 h_Delta0 := Hprime + 2*h; dF := (r + 1)*d; 
 
 # Delta1 
 hF := Hprime_prime; 
 dG := (r + 1)*d*D; 
 hG := h + d*(Hprime_prime + ln(n + 2)) + ln((r + 1)(n + 2))*(r + 1)*D; 
 s := (r + 1)*(n + 1); 
 h_Delta1 := Lemma2_6(dF, dG, hF, hG, s); 

 # Delta2 
 h_Delta2 := h_Delta1; 

 # h_Delta_V_G_sep_H
 h_Delta_V_G_sep_H := h_Delta0 + h_Delta1 + h_Delta2;
 h_Delta_V_G_sep_H := expand(h_Delta_V_G_sep_H); 
 h_Delta_V_G_sep_H := simplify(h_Delta_V_G_sep_H); 

 return h_Delta_V_G_sep_H; 
end proc:

Lemma4_9(n, r, d, D, h, H)
;

# ---------------------------------------------------------------
# Lemma 4.11
# ---------------------------------------------------------------
Lemma4_11 := proc(n, r, DV, HV, DW, HW) 
    local h_Delta0, h_Delta1, h_Delta2, h_DeltaVW_sep, d_Pprime, d_Gprime_P_prime, h_Pprime, h_Gprime_P_prime, s; 

    # Delta0 = c*g * lc(G')
    h_Delta0 := (HV + (r+1)*DV) + (HW) + (HW + (r+1)*DW*ln(n+2)); 

    # Delta1
    s := (r + 1)*n; 
    d_Pprime := (r + 1)*DV; 
    d_Gprime_P_prime := (r + 1)*DV*DW; 
    h_Pprime := HV + 2*(r + 1)*DV*ln(n + 2) + r*DV; 
    h_Gprime_P_prime := HW + DW*(HV + (r + 1)*DV*ln(n + 2) + 
r*DV + ln(DV) + ln(n + 2)) + ln((r + 1)*(n + 2))*(r + 1)*DV; 
    h_Delta1 := Lemma2_6(d_Pprime, d_Gprime_P_prime, h_Pprime, h_Gprime_P_prime, s);  

    # Delta2
    h_Delta2 := Lemma2_6((r+1)*DV, (r+1)*DV, HV + (r+1)*ln(n+2)*DV, HV + (r+1)*ln(n+2)*DV + ln(DV), s);
    # DeltaVW_sep
    h_DeltaVW_sep := h_Delta0 + h_Delta1 + h_Delta2;
    h_DeltaVW_sep := expand(h_DeltaVW_sep); 
    h_DeltaVW_sep := simplify(h_DeltaVW_sep);  

    return h_DeltaVW_sep; 
end proc:


Lemma4_11(n, r, DV, HV, DW, HW)
;

# ---------------------------------------------------------------
# Lemma 4.13
# ---------------------------------------------------------------
Lemma4_13 := proc(n, r, DV, HV, hF) 
 local Hprime, h_Delta0, h_Delta1, h_Delta_VF_Chow, D1, D2, H1, H2; 

 Hprime := HV + (r + 1)*ln(n + 2)*DV; 

 # Delta0
 h_Delta0 := Hprime + hF;

 # Delta1
 h_Delta1 := Lemma4_3(n, r, DV, DV, Hprime, Hprime); 
 
 # Delta_VF_Chow
 h_Delta_VF_Chow := h_Delta0 + h_Delta1; 
 h_Delta_VF_Chow := expand(h_Delta_VF_Chow);
 h_Delta_VF_Chow := simplify(h_Delta_VF_Chow);

 return simplify(expand(h_Delta_VF_Chow)); 
end proc:

Lemma4_13(n, r, DV, HV, hF)
;

# ---------------------------------------------------------------
# Lemma 4.18
# ---------------------------------------------------------------
Lemma4_18 := proc(n, r, dF, hF, DV, HV) 
 local h_Delta_VF_intersection, h_Delta_VF_Chow, h_Delta_3, h_Delta_2, h_Delta_1, dG, hG, s; 

 # Delta_VF_Chow
 h_Delta_VF_Chow := Lemma4_13(n, r, DV, HV, hF); 

 # Delta_1
 # Lemma 3.15
 h_Delta_1 := dF*HV + hF*DV + (r + 1)*ln(n + 1)*dF*DV; 

 # Delta_2
 # DW = dFDV
 # HW = dFHV + hFDV + ndFDVln(n+1)
 h_Delta_2 := dF*DV*ln(dF*DV); 
 
 # Delta_3
 s := n; 
 h_Delta_3 := Lemma2_6(dF*DV, dF*DV, dF*HV + hF*DV + n*dF*DV*ln(n + 1), dF*HV + hF*DV + n*dF*DV*ln(n + 1), s);
 # h_Delta_VF_intersection 
 h_Delta_VF_intersection := h_Delta_VF_Chow + h_Delta_3 + h_Delta_2 + h_Delta_1;
 h_Delta_VF_intersection := expand(h_Delta_VF_intersection);
 h_Delta_VF_intersection := simplify(h_Delta_VF_intersection); 

 return h_Delta_VF_intersection; 
end proc:


Lemma4_18(n, r, dF, hF, DV, HV)
;

# ===============================================================
# Main: bounding Delta' 
# ===============================================================

# ---------------------------------------------------------------
# subroutines
# ---------------------------------------------------------------

Proposition5_4 := proc(h_Delta_sep_H, h_Delta_int, h_Delta_union, h_Delta_sep, n,s) 
 local L, h_Delta_i; 
 h_Delta_i := sum(h_Delta_sep_H + h_Delta_int + h_Delta_union + sum(h_Delta_sep, l = k + 1 .. n), k = 0 .. n); 
 return simplify(1 + s*h_Delta_i); 
end proc:

SimplifyBound := proc(expr) 
 local tmp; 
 tmp := simplify(eval(expr, D = 2*d^(n + 1))); 
 tmp := simplify(eval(tmp, H = 5*h*n*d^(n + 1)*ln(n + 1))); 
 tmp := simplify(eval(tmp, r = n)); 
 return tmp; 
end proc:

# ---------------------------------------------------------------
# variables
# ---------------------------------------------------------------

h_delta := expand(n*(ln(3) + 2*ln(n) + (2*n + 2)*ln(d)) + n*ln(n))
;
hprime := h + n^2*d*ln(d)
;
Hprime := H + n^2*D*ln(D)
;

# ---------------------------------------------------------------
# Delta_prime bound 
# ---------------------------------------------------------------

h_Delta_sep_H := Lemma4_9(n, r, d, D, hprime, Hprime): 
h_Delta_int := Lemma4_18(n, r, d, hprime, D, Hprime): 
h_Delta_union := Lemma4_3(n, r, D, D, Hprime, Hprime): 
h_Delta_sep := Lemma4_11(n, r, D, Hprime, D, Hprime): 
h_Delta := Proposition5_4(h_Delta_sep_H, h_Delta_int, h_Delta_union, h_Delta_sep, n,s):
h_Delta := SimplifyBound(h_Delta):
h_Delta_prime := h_Delta + h_delta:
h_Delta_prime
;





# ===============================================================
# Experiments 
# ===============================================================

# ---------------------------------------------------------------
# Subroutines
# ---------------------------------------------------------------

height_bound_U_SOMBRA_et_al := proc(n, s, d, h)
    local C1, C2;
    C1 := 11*n + 4;
    C2 := (55*n + 99)*log((2*n + 5)*s);
    return evalf(C1 * d^(3*n + 1) * h + C2 * d^(3*n + 2));
end proc:

height_bound_Delta_prime := proc(h_Delta_prime_val, n_val, s_val, d_val, h_val)
    local tmp;

    # Substitute parameters
    tmp := subs(
        n = n_val,
        s = s_val,
        d = d_val,
        h = h_val,
        h_Delta_prime_val
    );

 
    # get numerical value 
    tmp := eval(tmp);
    tmp := evalf(tmp);

    return tmp;
end proc:

bounds := proc(n, s, d, h)
    local A, B;
    A := height_bound_U_SOMBRA_et_al(n, s, d, h);
    B := height_bound_Delta_prime(h_Delta_prime, n, s, d, h);
    return A, B, B/A;
end proc:


# ===============================================================
# Bounds / sweeps
# ===============================================================

# Sweep in n (number of variables)
n_vals := [1, 2, 5, 10, 20, 50]:
s := 5: d := 2: h := 10:
printf("=== Sweep in n (s=%d, d=%d, h=%d) ===\n", s, d, h);
printf("n\tA\t\tB\t\tB/A\n");
for n in n_vals do
    A, B, ratio := bounds(n, s, d, h);
    printf("%d\t%.4e\t%.4e\t%.4e\n", n, A, B, ratio);
end do:

# Sweep in s (number of equations)
s_vals := [2, 5, 10, 20, 50, 100]:
n := 5: d := 2: h := 10:
printf("\n=== Sweep in s (n=%d, d=%d, h=%d) ===\n", n, d, h);
printf("s\tA\t\tB\t\tB/A\n");
for s in s_vals do
    A, B, ratio := bounds(n, s, d, h);
    printf("%d\t%.4e\t%.4e\t%.4e\n", s, A, B, ratio);
end do:

# Sweep in d (degree)
d_vals := [2, 3, 5, 10, 20]:
n := 3: s := 5: h := 10:
printf("\n=== Sweep in d (n=%d, s=%d, h=%d) ===\n", n, s, h);
printf("d\tA\t\tB\t\tB/A\n");
for d in d_vals do
    A, B, ratio := bounds(n, s, d, h);
    printf("%d\t%.4e\t%.4e\t%.4e\n", d, A, B, ratio);
end do:

# Sweep in h (coefficient height)
h_vals := [1, 2, 5, 10, 100]:
n := 3: s := 5: d := 3:
printf("\n=== Sweep in h (n=%d, s=%d, d=%d) ===\n", n, s, d);
printf("h\tA\t\tB\t\tB/A\n");
for h in h_vals do
    A, B, ratio := bounds(n, s, d, h);
    printf("%d\t%.4e\t%.4e\t%.4e\n", h, A, B, ratio);
end do:











