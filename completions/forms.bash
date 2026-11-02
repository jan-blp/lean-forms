# Complete forms and forms-web, directly or through Lake.
_forms_complete() {
    local start=1 cursor=$COMP_CWORD word executable
    local -a invoke
    COMPREPLY=()
    if [[ ${COMP_WORDS[0]##*/} == lake ]]; then
        while [[ ${COMP_WORDS[start]} == -q || ${COMP_WORDS[start]} == --quiet ]]; do
            ((start += 1))
        done
        executable=${COMP_WORDS[start+1]}
        if [[ ${COMP_WORDS[start]} != exe || ( $executable != forms && $executable != forms-web ) ]] || ((cursor < start + 2)); then
            if [[ -n ${_forms_previous_lake_completion:-} ]]; then
                "$_forms_previous_lake_completion" "$@"
            fi
            return 0
        fi
        ((start += 2))
        invoke=("${COMP_WORDS[0]}" -q exe "$executable")
    else
        invoke=("${COMP_WORDS[0]}")
    fi
    ((cursor >= start)) || return 0
    while IFS= read -r word; do
        COMPREPLY+=("$word")
    done < <("${invoke[@]}" --complete "${COMP_WORDS[@]:start:cursor-start}" "${COMP_WORDS[cursor]}" 2>/dev/null)
}

# Preserve an existing Lake completion function for unrelated Lake commands.
_forms_existing_completion=$(complete -p lake 2>/dev/null || :)
if [[ $_forms_existing_completion =~ -F[[:space:]]+([^[:space:]]+) ]] && [[ ${BASH_REMATCH[1]} != _forms_complete ]]; then
    _forms_previous_lake_completion=${BASH_REMATCH[1]}
fi
unset _forms_existing_completion
complete -F _forms_complete forms forms-web .lake/build/bin/forms .lake/build/bin/forms-web
complete -o default -F _forms_complete lake
