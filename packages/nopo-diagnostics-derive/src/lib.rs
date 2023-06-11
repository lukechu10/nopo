use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{parse2, parse_macro_input, Data, DeriveInput, LitStr, Meta, Result, Token};

#[proc_macro_derive(IntoReport, attributes(label, message, kind))]
pub fn into_report(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let tokens = impl_into_report(input);
    proc_macro::TokenStream::from(tokens.unwrap_or_else(|err| err.into_compile_error()))
}

fn impl_into_report(input: DeriveInput) -> Result<TokenStream> {
    let Data::Struct(data) = input.data else {
        return Err(syn::Error::new(
            input.span(),
            "Report can only be derived on a struct",
        ));
    };

    let ident = &input.ident;

    let kind = input
        .attrs
        .iter()
        .find_map(|attr| match &attr.meta {
            Meta::List(meta) if meta.path.is_ident("kind") => Some(&meta.tokens),
            _ => None,
        })
        .cloned()
        .map(parse2::<LitStr>)
        .ok_or_else(|| syn::Error::new(input.ident.span(), "Missing #[kind] attribute"))??;
    let message = input
        .attrs
        .iter()
        .find_map(|attr| match &attr.meta {
            Meta::List(meta) if meta.path.is_ident("message") => Some(&meta.tokens),
            _ => None,
        })
        .cloned()
        .map(parse2::<LitStr>)
        .ok_or_else(|| syn::Error::new(input.ident.span(), "Missing #[message] attribute"))??;

    let kind = match kind.value().as_str() {
        "error" => quote!(::nopo_diagnostics::ariadne::ReportKind::Error),
        "warning" => quote!(::nopo_diagnostics::ariadne::ReportKind::Warning),
        "advice" => quote!(::nopo_diagnostics::ariadne::ReportKind::Advice),
        _ => {
            return Err(syn::Error::new(
                input.ident.span(),
                "Report kind should be one of `error`, `warning`, or `advice`",
            ))
        }
    };

    let fields = match &data.fields {
        syn::Fields::Named(fields) => &fields.named,
        _ => {
            return Err(syn::Error::new(
                data.fields.span(),
                "Report can not be derived on a tuple or unit struct",
            ))
        }
    };
    let field_idents = fields
        .iter()
        .map(|field| field.ident.as_ref().expect("not tuple struct"))
        .collect::<Vec<_>>();
    let span = fields
        .iter()
        .find(|field| field.ident.as_ref().expect("not tuple struct") == "span")
        .ok_or_else(|| syn::Error::new(input.ident.span(), "Missing `span` field"))?
        .ident
        .as_ref()
        .unwrap();

    let labels = fields
        .iter()
        .map(|field| {
            field.attrs.iter().find_map(|attr| match &attr.meta {
                Meta::List(meta) if meta.path.is_ident("label") => {
                    Some(parse2::<LabelMeta>(meta.tokens.clone()))
                }
                _ => None,
            })
        })
        .map(Option::transpose)
        .collect::<Result<Vec<_>>>()?;

    let labels = fields
        .iter()
        .zip(labels.iter())
        .filter_map(|(field, label)| label.as_ref().and_then(|label| Some((field, label))))
        .map(|(field, label)| {
            let ident = field.ident.as_ref().expect("not tuple struct");
            let message = &label.value;
            quote! {
                .with_label(
                    ::nopo_diagnostics::Label::new(<_ as ::nopo_diagnostics::span::GetSpan>::span(&#ident))
                        .with_message(::std::format!(#message)),
                )
            }
        });

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    Ok(quote! {
        impl #impl_generics ::nopo_diagnostics::IntoReport for #ident #ty_generics #where_clause {
            fn into_report(self) -> ::nopo_diagnostics::Report {
                let #ident { #(#field_idents),* } = self;
                ::nopo_diagnostics::Report::build(#kind, #span.file_id, #span.start as usize)
                    .with_message(::std::format!(#message))
                    #(#labels)*
                    .finish()
            }
        }
    })
}

mod kw {
    syn::custom_keyword!(message);
}

struct LabelMeta {
    _message_ident: kw::message,
    _eq: Token![=],
    value: LitStr,
}

impl Parse for LabelMeta {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            _message_ident: input.parse()?,
            _eq: input.parse()?,
            value: input.parse()?,
        })
    }
}
