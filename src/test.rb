require 'tempfile'

def     create_and_execute_tmp_file(entree, options)

    value = ""
    Tempfile.create { |f| 
        f << entree;
        f.rewind;
        value = `./a.out #{f.path} #{options}`
    }
    return value
end

def     compare_expected_result(path)

    # Read the file in one string
    text = File.read(path)
    
    # Parse with Regex
    entree = text.scan(/\[Entree\]((.|\n)*?)\[Sortie\]/)[0][0]
    sortie = text.scan(/\[Sortie\]((.|\n)*?)\[options\]/)[0][0].delete("\n")
    options = text.scan(/\[options\]((.|\n)*)$/)[0][0].delete("\n")

    # Retrieve execution output
    ret_value = create_and_execute_tmp_file(entree, options).delete("\n")

    # Output
    if (sortie == ret_value) then
        puts "#{path[2..]} -> [\e[32mok\e[0m]"
    else
        puts "#{path[2..]} -> [\e[31mko\e[0m]"
    end

end


def     main()

    compare_expected_result('./format_test')

end

main()