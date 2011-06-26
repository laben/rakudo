class Nil { ... }

my &THROW :=
    -> |$ {
        Q:PIR {
            .local pmc args, payload, type, severity, ex
            args = perl6_current_args_rpa
            payload  = args[0]
            type     = args[1]
            severity = args[2]
            unless null severity goto have_severity
            severity = box .EXCEPT_NORMAL
          have_severity:
            ex = root_new ['parrot';'Exception']
            setattribute ex, 'payload', payload
            setattribute ex, 'type', type
            setattribute ex, 'severity', severity
            throw ex
        };
        0
    };

my &return-rw := -> \$parcel = Nil { 
    THROW($parcel, pir::const::CONTROL_RETURN) 
};
my &return := -> \$parcel = Nil { 
    THROW(pir::perl6_decontainerize__PP($parcel), 
          pir::const::CONTROL_RETURN) 
};

my &take-rw := -> \$parcel = Nil { 
    THROW($parcel, pir::const::CONTROL_TAKE) 
};
my &take := -> \$parcel = Nil { 
    THROW(pir::perl6_decontainerize__PP($parcel), 
          pir::const::CONTROL_TAKE) 
};

my &last := -> \$parcel = Nil { 
    THROW(pir::perl6_decontainerize__PP($parcel), 
          pir::const::CONTROL_LOOP_LAST) 
};

my &next := -> \$parcel = Nil { 
    THROW(pir::perl6_decontainerize__PP($parcel), 
          pir::const::CONTROL_LOOP_NEXT) 
};

my &redo := -> \$parcel = Nil { 
    THROW(pir::perl6_decontainerize__PP($parcel), 
          pir::const::CONTROL_LOOP_REDO) 
};

my &succeed := -> \$parcel = Nil { 
    THROW(pir::perl6_decontainerize__PP($parcel), 
          pir::const::CONTROL_BREAK) 
};

my &proceed := -> {
    THROW(Nil, pir::const::CONTROL_CONTINUE)
}

sub die(*@msg) { pir::die(@msg.join('')) }
sub fail(*@msg) { pir::die(@msg.join('')) }

sub eval(Str $code, :$lang = 'perl6') {
    my $caller_ctx := Q:PIR {
        $P0 = getinterp
        %r = $P0['context';1]
    };
    my $caller_lexpad := Q:PIR {
        $P0 = getinterp
        %r = $P0['lexpad';1]
    };
    my $result;
    my $success;
    try {
        my $compiler := pir::compreg__PS($lang);
        my $pbc      := $compiler.compile($code, :outer_ctx($caller_ctx));
        nqp::atpos($pbc, 0).set_outer_ctx($caller_ctx);
        $result := $pbc();
        $success = 1;
    }
    nqp::bindkey($caller_lexpad, '$!', $!);
    $success ?? $result !! Any # XXX fail($!)
}
