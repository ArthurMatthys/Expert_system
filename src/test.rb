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

    text = File.read(path)
    entree = text.scan(/\[Entree\]((.|\n)*?)\[Sortie\]/)[0][0]
    sortie = text.scan(/\[Sortie\]((.|\n)*?)\[options\]/)[0][0].delete("\n")
    options = text.scan(/\[options\]((.|\n)*)$/)[0][0].delete("\n")
    ret_value = create_and_execute_tmp_file(entree, options).delete("\n")

    puts entree

    if (sortie == ret_value) then
        puts "The test is a success"
    else
        puts "The test is an error"
    end

end


def     main()

    compare_expected_result('./format_test')

end

main()