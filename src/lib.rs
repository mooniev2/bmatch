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

fn mask_and_ty_to_lit(str_str: &str, ty: &Type) -> LitInt {
    let ty = quote!(#ty).to_string();
    LitInt::new(&format!("0b0{str_str}{ty}"), Span::call_site())
}

struct VarMask {
    ident: Ident,
    start_bit: usize,
    length: usize,
}

fn mask_str_to_ty(str: &str) -> Type {
    if str.len() > 128 {
        panic!("bit string cannot exceed a bit width of 128.")
    } else if str.len() > 64 {
        parse_quote!(u128)
    } else if str.len() > 32 {
        parse_quote!(u64)
    } else if str.len() > 16 {
        parse_quote!(u32)
    } else if str.len() > 8 {
        parse_quote!(u16)
    } else {
        parse_quote!(u8)
    }
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
                '0' | '1' => true,
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

fn mask_str_to_lit(mask: &str, ty: &Type) -> (LitInt, LitInt, bool) {
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
        mask_and_ty_to_lit(&mask, &ty),
        mask_and_ty_to_lit(&expect, &ty),
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
                        '_' | '-' => false,
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
            let ty = mask_str_to_ty(&mask);
            let vars = collect_vars_from_mask(&mask);
            let declr_vars = vars.iter().map(|var| {
                let ident = &var.ident;
                let mask = LitInt::new(&((1 << var.length) - 1).to_string(), Span::call_site());
                let shift = var.start_bit;
                quote::quote!(let #ident = (#mask_ident >> #shift) & #mask)
            });
            let (int_mask, int_expect, irrefutable) = mask_str_to_lit(&mask, &ty);
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
