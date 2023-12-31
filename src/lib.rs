use std::collections::BTreeSet;

use peeking_take_while::PeekableExt;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::token::If;
use syn::{
    parse_macro_input, parse_quote, Arm, Attribute, Expr, ExprMatch, Lit, LitInt, Token, Type,
};

enum BArm {
    Masked {
        mask: String,
        guard: Option<(If, Box<Expr>)>,
        body: Box<Expr>,
    },
    Any {
        guard: Option<(If, Box<Expr>)>,
        body: Box<Expr>,
        comma: Option<Token!(,)>,
    },
}

struct BMatch {
    attrs: Vec<Attribute>,
    expr: Box<Expr>,
    barms: Vec<BArm>,
}

fn mask_and_ty_to_lit(str_str: &str) -> LitInt {
    LitInt::new(&format!("0b0{str_str}"), Span::call_site())
}

struct VarMask {
    ident: Ident,
    start_bit: usize,
    length: usize,
}

fn collect_vars_from_mask(mask: &str) -> Vec<VarMask> {
    let mut masks = vec![];
    let mut iter = mask.chars().rev().peekable();
    let mut bit_pos = 0;
    let mut collected_idents = BTreeSet::new();
    while iter.peek().is_some() {
        let former_bit_pos = bit_pos;
        bit_pos += iter
            .by_ref()
            .peeking_take_while(|c| match c {
                '0' | '1' | '-' => true,
                _ => false,
            })
            .count();
        let Some(&peek) = iter.peek() else {
            break;
        };
        match peek {
            c if c.is_alphabetic() => {
                assert!(collected_idents.insert(c), "identifier '{c}' is fragmented");
                let length = iter.by_ref().peeking_take_while(|&cmp| cmp == c).count();
                bit_pos += length;
                masks.push(VarMask {
                    ident: Ident::new(&c.to_string(), Span::call_site()),
                    start_bit: former_bit_pos,
                    length,
                })
            }
            c => panic!("expected an alphabetic identifier, got '{c}'"),
        }
    }
    masks
}

fn mask_str_to_lit(mask: &str) -> (LitInt, LitInt, bool) {
    let mut irrefutable = true;
    let (mask, expect) = mask
        .chars()
        .map(|c| match c {
            '0' => {
                irrefutable = false;
                ('1', '0')
            }
            '1' => {
                irrefutable = false;
                ('1', '1')
            }
            '-' => ('0', '0'),
            _ => ('0', '0'),
        })
        .fold(
            (String::with_capacity(128), String::with_capacity(128)),
            |(mut mask, mut expect), (mask_new, expect_new)| {
                mask.push(mask_new);
                expect.push(expect_new);
                (mask, expect)
            },
        );
    (
        mask_and_ty_to_lit(&mask),
        mask_and_ty_to_lit(&expect),
        irrefutable,
    )
}

fn visit_arm(arm: Arm) -> BArm {
    assert!(
        arm.attrs.is_empty(),
        "cannot use attributes on bitmatch arm"
    );
    match arm.pat {
        syn::Pat::Lit(syn::PatLit {
            attrs,
            lit: Lit::Str(str),
        }) => {
            assert!(
                attrs.is_empty(),
                "unable to use attributes for a mask in a bitmatch arm"
            );
            BArm::Masked {
                guard: arm.guard,
                mask: str
                    .value()
                    .chars()
                    .filter(|c| match c {
                        '_' => false,
                        _ => true,
                    })
                    .collect(),
                body: arm.body,
            }
        }

        syn::Pat::Wild(_) => BArm::Any {
            guard: arm.guard,
            body: arm.body,
            comma: arm.comma,
        },
        _ => panic!("expected string literal in arm"),
    }
}

fn visit_match(mexpr: ExprMatch) -> BMatch {
    let mut barms = vec![];
    for arm in mexpr.arms {
        barms.push(visit_arm(arm));
    }
    BMatch {
        attrs: mexpr.attrs,
        expr: mexpr.expr,
        barms,
    }
}

fn bmatch_to_tokens(bmatch: BMatch) -> TokenStream {
    let outer_attrs = bmatch.attrs;
    let match_expr = bmatch.expr;
    let arm_iter = bmatch.barms.into_iter().map(|arm| match arm {
        BArm::Masked { mask, guard, body } => {
            let mask_ident = Ident::new("_mask_", Span::call_site());
            assert!(mask.len() <= 128, "bit string cannot exceed a bit width of 128.");
            let vars = collect_vars_from_mask(&mask);
            let declr_vars = vars.iter().map(|var| {
                let ident = &var.ident;
                let mask = LitInt::new(&((1 << var.length) - 1).to_string(), Span::call_site());
                let shift = var.start_bit;
                if var.length == 1 {
                    quote::quote!(#[allow(non_snake_case)] let #ident = (#mask_ident >> #shift) & #mask != 0)
                } else {
                    quote::quote!(#[allow(non_snake_case)] let #ident = (#mask_ident >> #shift) & #mask)
                }
            });
            let (int_mask, int_expect, irrefutable) = mask_str_to_lit(&mask);
            let guard = if let Some(guard) = guard {
                let inner_expr = &guard.1;
                let declr_vars = declr_vars.clone();
                quote::quote!( && { #(#declr_vars;)* #inner_expr } )
            } else {
                quote::quote!()
            };
            if irrefutable {
                quote::quote!(
                    #mask_ident #guard => {
                        #(#declr_vars;)*
                        #body
                    }
                )
            } else {
                quote::quote!(
                    #mask_ident if #mask_ident & #int_mask == #int_expect #guard => {
                        #(#declr_vars;)*
                        #body
                    }
                )
            }
        }
        BArm::Any { guard, body, comma } => {
            let guard = if let Some((if_kw, expr)) = guard {
                quote::quote!(#if_kw #expr)
            } else {
                quote::quote!()
            };
            quote::quote!(_ #guard => #body #comma)
        }
    });
    quote::quote!(
        #(#outer_attrs)*
        match #match_expr {
            #(#arm_iter)*
        }
    )
    .into()
}

#[proc_macro]
pub fn bitmatch(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::ExprMatch);
    let output = visit_match(input);
    bmatch_to_tokens(output)
}
