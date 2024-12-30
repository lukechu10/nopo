use proc_macro2::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::{parse2, parse_macro_input, Data, DeriveInput, LitInt, LitStr, Meta, Result, Token};

#[proc_macro_derive(Report, attributes(label, message, kind))]
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
                    Some(parse2::<LabelData>(meta.tokens.clone()))
                }
                _ => None,
            })
        })
        .map(Option::transpose)
        .collect::<Result<Vec<_>>>()?;

    let labels = fields
        .iter()
        .zip(labels.iter())
        .filter_map(|(field, label)| label.as_ref().map(|label| (field, label)))
        .map(|(field, label)| {
            let ident = field.ident.as_ref().expect("not tuple struct");
            let message = &label.message.value;
            let order = label.order.as_ref().map(|order| order.value.base10_parse().expect("could not parse order")).unwrap_or(0);
            quote! {
                .with_label(
                    ::nopo_diagnostics::Label::new(<_ as ::nopo_diagnostics::span::GetSpan>::span(&#ident))
                        .with_message(::std::format!(#message))
                        .with_order(#order),
                )
            }
        });

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    Ok(quote! {
        impl #impl_generics ::nopo_diagnostics::IntoReport for #ident #ty_generics #where_clause {
            fn into_report(self) -> ::nopo_diagnostics::ReportBuilder {
                let #ident { #(#field_idents),* } = self;
                ::nopo_diagnostics::Report::build(#kind, #span.file_id, #span.start as usize)
                    .with_message(::std::format!(#message))
                    #(#labels)*
            }
        }
    })
}

mod kw {
    syn::custom_keyword!(message);
    syn::custom_keyword!(order);
}

struct LabelMeta<Kw, E> {
    _message_ident: Kw,
    _eq: Token![=],
    value: E,
}

impl<Kw: Parse, E: Parse> Parse for LabelMeta<Kw, E> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            _message_ident: input.parse()?,
            _eq: input.parse()?,
            value: input.parse()?,
        })
    }
}

struct LabelData {
    message: LabelMeta<kw::message, LitStr>,
    _comma: Option<Token![,]>,
    order: Option<LabelMeta<kw::order, LitInt>>,
}

impl Parse for LabelData {
    fn parse(input: ParseStream) -> Result<Self> {
        let message = input.parse()?;
        let (_comma, order) = if input.peek(Token![,]) {
            (Some(input.parse()?), Some(input.parse()?))
        } else {
            Default::default()
        };
        Ok(Self {
            message,
            _comma,
            order,
        })
    }
}
