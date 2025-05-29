pragma circom 2.0.0;

template main_template() {
    signal input a;
    signal input b;

    signal output out;

    out <== a * (b * 0 + 1);
}

component main = main_template();