FROM debian:jessie

RUN apt-get update -q \
    && apt-get install -y --no-install-recommends \
        bsdutils \
        bsdmainutils \ 
        build-essential \
        ca-certificates \
        gcc \
        git \
        locales \
        mlton \
        time \
        exim4 \
        mailutils \
    && apt-get clean autoclean \
    && apt-get autoremove --yes \
    && rm -rf /var/lib/{apt,dpkg,cache,log}/ \
    && echo 'en_AU.UTF-8 UTF-8' > /etc/locale.gen \
    && dpkg-reconfigure --frontend=noninteractive locales \
    && echo "LANG=en_AU.UTF-8" >> /etc/default/locale 

ENV LANG en_AU.UTF-8

# All this junk + exim4 and mailutils from above is to enable proper sendmail functionality
# from CSIRO virtual machines within a jenkins spawned Docker container
RUN echo "dc_eximconfig_configtype='satellite'" > /etc/exim4/update-exim4.conf.conf \
    && echo "dc_other_hostnames='remote_agent.keg.data61.csiro.au'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_local_interfaces='127.0.0.1 ; ::1'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_readhost='data61.csiro.au'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_relay_domains=''" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_minimaldns='false'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_relay_nets=''" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_smarthost='smtp.csiro.au'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "" >> /etc/exim4/update-exim4.conf.conf \
    && echo "CFILEMODE='644'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_use_split_config='true'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_hide_mailname='true'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_mailname_in_oh='true'" >> /etc/exim4/update-exim4.conf.conf \
    && echo "dc_localdelivery='mail_spool'" >> /etc/exim4/update-exim4.conf.conf \
    && useradd -u 1000 jenkins \
    && echo "1000:	root" >> /etc/aliases \
    && echo "root: bamboo@ertos.nicta.com.au" >> /etc/email-addresses \
    && echo 'root@* "${lookup{${local_part}}lsearch{/etc/email-addresses} {$value}fail}" Ffrs' > /etc/exim4/conf.d/rewrite/ertos_rewrite \
    && update-exim4.conf && service exim4 restart

