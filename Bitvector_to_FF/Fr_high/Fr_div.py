void Fr_div(PFrElement r, PFrElement a, PFrElement b) {
    FrElement tmp;
    Fr_inv(&tmp, b);
    Fr_mul(r, a, &tmp);
}