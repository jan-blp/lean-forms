# Build PDFs with XeLaTeX.
$pdf_mode = 5;
$xelatex = 'xelatex -interaction=nonstopmode -halt-on-error -file-line-error %O %S';

# Regenerate the TeX source when Org changes, including in watch mode.
add_cus_dep('org', 'tex', 0, 'org_to_tex');
sub org_to_tex {
    return system('make', "$_[0].tex");
}

# Rebuild included Graphviz diagrams in watch mode.
add_cus_dep('dot', 'pdf', 0, 'dot_to_pdf');
sub dot_to_pdf {
    return system('make', "$_[0].pdf");
}
